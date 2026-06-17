//! Benchmark harness (benchmarking-and-performance-methodology note).
//!
//! Walks a corpus directory of `.smt2` files, runs each through the solver
//! trait, and emits a versioned JSON results artifact: per-instance result,
//! ground-truth agreement, layer-attributed timing, and PAR-2 scoring.
//! Disagreement with a benchmark's `:status` is a soundness alarm and makes
//! the run exit nonzero.
//!
//! Usage: `axeyum-bench <dir> [--timeout-ms N] [--limit N] [--out FILE]`
//!   `[--corpus-source TEXT] [--logic LOGIC] [--families CSV] [--seed TEXT]`
//!   `[--rewrite off|default] [--backend sat-bv|z3]`
//!   `[--query-plan full|first-assertion-support|replay-refine|replay-refine-exact]`
//!   `[--refine-rounds N] [--refine-batch N] [--refine-adaptive-batch]`
//!   `[--refine-select first|smallest-dag|smallest-plan-dag|smallest-plan-greedy]`
//!   `[--node-budget N] [--cnf-var-budget N] [--cnf-clause-budget N]`
//!   `[--compare-z3] [--jobs N]`
//! The default build can run the pure Rust `sat-bv` backend. Build with
//! `--features z3` (or `z3-static`) to enable the Z3 oracle backend.

fn main() -> std::process::ExitCode {
    run::main()
}

mod run {
    use std::collections::BTreeMap;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::ExitCode;
    use std::time::Duration;

    use axeyum_ir::{TermArena, TermId, TermStats, Value, eval};
    use axeyum_query::{Query, QueryPlan, StructuralCacheKey};
    use axeyum_rewrite::{
        ModelReconstructionTrail, RewriteReport, canonicalize_terms, default_manifest,
        propagate_values, solve_eqs,
    };
    use axeyum_smtlib::{Script, SmtError, parse_script};
    #[cfg(feature = "z3")]
    use axeyum_solver::Z3Backend;
    use axeyum_solver::{
        BvLayerStats, CheckResult, Model, SatBvBackend, SolveStats, SolverBackend, SolverConfig,
        SolverError, UnknownKind,
    };
    use rayon::prelude::*;
    use serde_json::{Value as JsonValue, json};

    const ARTIFACT_VERSION: u32 = 14;
    /// Corpus SAT-share threshold above which SAT solve time is reported as
    /// dominating end-to-end time — gate (a) for prioritizing the custom CDCL
    /// core (benchmarking-and-performance-methodology.md, "Decision Gates").
    const SAT_DOMINATES_SHARE: f64 = 0.5;
    const PLAN_REFINE_SCORE_CANDIDATES: usize = 64;
    const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum RewriteMode {
        Off,
        Default,
    }

    impl RewriteMode {
        fn as_str(self) -> &'static str {
            match self {
                RewriteMode::Off => "off",
                RewriteMode::Default => "default",
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum BackendKind {
        SatBv,
        #[cfg(feature = "z3")]
        Z3,
    }

    impl BackendKind {
        fn as_str(self) -> &'static str {
            match self {
                BackendKind::SatBv => "sat-bv",
                #[cfg(feature = "z3")]
                BackendKind::Z3 => "z3",
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum QueryPlanMode {
        Full,
        FirstAssertionSupport,
        ReplayRefine,
        ReplayRefineExact,
    }

    impl QueryPlanMode {
        fn as_str(self) -> &'static str {
            match self {
                QueryPlanMode::Full => "full",
                QueryPlanMode::FirstAssertionSupport => "first-assertion-support",
                QueryPlanMode::ReplayRefine => "replay-refine",
                QueryPlanMode::ReplayRefineExact => "replay-refine-exact",
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum RefineSelectMode {
        First,
        SmallestDag,
        SmallestPlanDag,
        SmallestPlanGreedy,
    }

    impl RefineSelectMode {
        fn as_str(self) -> &'static str {
            match self {
                RefineSelectMode::First => "first",
                RefineSelectMode::SmallestDag => "smallest-dag",
                RefineSelectMode::SmallestPlanDag => "smallest-plan-dag",
                RefineSelectMode::SmallestPlanGreedy => "smallest-plan-greedy",
            }
        }
    }

    const DEFAULT_REFINE_ROUNDS: usize = 16;

    #[derive(Debug, Clone, Copy)]
    struct PlanSolveConfig {
        mode: QueryPlanMode,
        refine_rounds: usize,
        refine_batch: usize,
        refine_adaptive_batch: bool,
        refine_select: RefineSelectMode,
    }

    impl PlanSolveConfig {
        fn from_args(args: &Args) -> Self {
            Self {
                mode: args.query_plan,
                refine_rounds: args.refine_rounds,
                refine_batch: args.refine_batch,
                refine_adaptive_batch: args.refine_adaptive_batch,
                refine_select: args.refine_select,
            }
        }

        fn uses_replay_refinement(self) -> bool {
            matches!(
                self.mode,
                QueryPlanMode::ReplayRefine | QueryPlanMode::ReplayRefineExact
            )
        }

        fn exact_targets(self) -> bool {
            self.mode == QueryPlanMode::ReplayRefineExact
        }
    }

    // A CLI argument bag: each independent flag is naturally its own bool.
    #[allow(clippy::struct_excessive_bools)]
    struct Args {
        dir: PathBuf,
        timeout_ms: u64,
        limit: usize,
        out: Option<PathBuf>,
        corpus_source: Option<String>,
        logic: Option<String>,
        families: Vec<String>,
        seed: String,
        rewrite: RewriteMode,
        backend: BackendKind,
        query_plan: QueryPlanMode,
        refine_rounds: usize,
        refine_batch: usize,
        refine_adaptive_batch: bool,
        refine_select: RefineSelectMode,
        node_budget: Option<u64>,
        cnf_variable_budget: Option<u64>,
        cnf_clause_budget: Option<u64>,
        cnf_inprocessing: bool,
        preprocess: bool,
        compare_z3: bool,
        jobs: usize,
    }

    fn parse_args() -> Result<Args, String> {
        let mut args = std::env::args().skip(1);
        let dir = PathBuf::from(args.next().ok_or("usage: axeyum-bench <dir> [options]")?);
        let mut parsed = Args {
            dir,
            timeout_ms: 5000,
            limit: usize::MAX,
            out: None,
            corpus_source: None,
            logic: None,
            families: Vec::new(),
            seed: "none".to_owned(),
            rewrite: RewriteMode::Off,
            backend: default_backend_kind(),
            query_plan: QueryPlanMode::Full,
            refine_rounds: DEFAULT_REFINE_ROUNDS,
            refine_batch: 1,
            refine_adaptive_batch: false,
            refine_select: RefineSelectMode::First,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            cnf_inprocessing: false,
            preprocess: false,
            compare_z3: false,
            jobs: 1,
        };
        while let Some(flag) = args.next() {
            parse_option(&mut parsed, &flag, &mut args)?;
        }
        validate_args(&parsed)?;
        Ok(parsed)
    }

    fn parse_option(
        parsed: &mut Args,
        flag: &str,
        args: &mut impl Iterator<Item = String>,
    ) -> Result<(), String> {
        match flag {
            "--timeout-ms" => {
                parsed.timeout_ms = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
            "--limit" => {
                parsed.limit = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
            "--out" => parsed.out = Some(PathBuf::from(next_value(args, flag)?)),
            "--corpus-source" => parsed.corpus_source = Some(next_value(args, flag)?),
            "--logic" => parsed.logic = Some(next_value(args, flag)?),
            "--families" => {
                parsed.families = next_value(args, flag)?
                    .split(',')
                    .map(str::trim)
                    .filter(|family| !family.is_empty())
                    .map(ToOwned::to_owned)
                    .collect();
            }
            "--seed" => parsed.seed = next_value(args, flag)?,
            "--rewrite" => {
                parsed.rewrite = match next_value(args, flag)?.as_str() {
                    "off" => RewriteMode::Off,
                    "default" => RewriteMode::Default,
                    other => return Err(format!("unknown rewrite mode `{other}`")),
                };
            }
            "--backend" => parsed.backend = parse_backend(&next_value(args, flag)?)?,
            "--query-plan" => parsed.query_plan = parse_query_plan(&next_value(args, flag)?)?,
            "--refine-rounds" => {
                parsed.refine_rounds = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
            "--refine-batch" => {
                parsed.refine_batch = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
                if parsed.refine_batch == 0 {
                    return Err("`--refine-batch` must be at least 1".to_owned());
                }
            }
            "--refine-adaptive-batch" => parsed.refine_adaptive_batch = true,
            "--refine-select" => {
                parsed.refine_select = parse_refine_select(&next_value(args, flag)?)?;
            }
            "--node-budget" => {
                parsed.node_budget = Some(
                    next_value(args, flag)?
                        .parse()
                        .map_err(|e| format!("{e}"))?,
                );
            }
            "--cnf-var-budget" => {
                parsed.cnf_variable_budget = Some(
                    next_value(args, flag)?
                        .parse()
                        .map_err(|e| format!("{e}"))?,
                );
            }
            "--cnf-clause-budget" => {
                parsed.cnf_clause_budget = Some(
                    next_value(args, flag)?
                        .parse()
                        .map_err(|e| format!("{e}"))?,
                );
            }
            "--inprocess" => parsed.cnf_inprocessing = true,
            "--preprocess" => parsed.preprocess = true,
            "--compare-z3" => {
                #[cfg(feature = "z3")]
                {
                    parsed.compare_z3 = true;
                }
                #[cfg(not(feature = "z3"))]
                {
                    return Err(
                        "`--compare-z3` requires building axeyum-bench with --features z3"
                            .to_owned(),
                    );
                }
            }
            "--jobs" => {
                parsed.jobs = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
                if parsed.jobs == 0 {
                    return Err("`--jobs` must be at least 1".to_owned());
                }
            }
            other => return Err(format!("unknown flag `{other}`")),
        }
        Ok(())
    }

    fn next_value(args: &mut impl Iterator<Item = String>, flag: &str) -> Result<String, String> {
        args.next().ok_or(format!("missing value for {flag}"))
    }

    fn validate_args(args: &Args) -> Result<(), String> {
        if args.refine_adaptive_batch
            && !matches!(
                args.query_plan,
                QueryPlanMode::ReplayRefine | QueryPlanMode::ReplayRefineExact
            )
        {
            return Err(
                "`--refine-adaptive-batch` requires `--query-plan replay-refine` or `replay-refine-exact`"
                    .to_owned(),
            );
        }
        if args.preprocess
            && matches!(
                args.query_plan,
                QueryPlanMode::ReplayRefine | QueryPlanMode::ReplayRefineExact
            )
        {
            return Err(
                "`--preprocess` is not yet supported with the replay-refinement query plans"
                    .to_owned(),
            );
        }
        Ok(())
    }

    #[cfg(feature = "z3")]
    fn default_backend_kind() -> BackendKind {
        BackendKind::Z3
    }

    #[cfg(not(feature = "z3"))]
    fn default_backend_kind() -> BackendKind {
        BackendKind::SatBv
    }

    fn parse_backend(value: &str) -> Result<BackendKind, String> {
        match value {
            "sat-bv" => Ok(BackendKind::SatBv),
            "z3" => {
                #[cfg(feature = "z3")]
                {
                    Ok(BackendKind::Z3)
                }
                #[cfg(not(feature = "z3"))]
                {
                    Err("backend `z3` requires building axeyum-bench with --features z3".to_owned())
                }
            }
            other => Err(format!("unknown backend `{other}`")),
        }
    }

    fn parse_query_plan(value: &str) -> Result<QueryPlanMode, String> {
        match value {
            "full" => Ok(QueryPlanMode::Full),
            "first-assertion-support" => Ok(QueryPlanMode::FirstAssertionSupport),
            "replay-refine" => Ok(QueryPlanMode::ReplayRefine),
            "replay-refine-exact" => Ok(QueryPlanMode::ReplayRefineExact),
            other => Err(format!("unknown query plan mode `{other}`")),
        }
    }

    fn parse_refine_select(value: &str) -> Result<RefineSelectMode, String> {
        match value {
            "first" => Ok(RefineSelectMode::First),
            "smallest-dag" => Ok(RefineSelectMode::SmallestDag),
            "smallest-plan-dag" => Ok(RefineSelectMode::SmallestPlanDag),
            "smallest-plan-greedy" => Ok(RefineSelectMode::SmallestPlanGreedy),
            other => Err(format!("unknown refinement selection mode `{other}`")),
        }
    }

    #[derive(Default)]
    struct Summary {
        files: u64,
        unsupported: u64,
        sat: u64,
        unsat: u64,
        unknown: u64,
        errors: u64,
        agree: u64,
        disagree: u64,
        model_replay_failures: u64,
        rewrite_changed_instances: u64,
        rewrite_applications: u64,
        rewrite_input_dag_nodes: u64,
        rewrite_output_dag_nodes: u64,
        rewrite_input_tree_nodes: u64,
        rewrite_output_tree_nodes: u64,
        rewrite_decision_matches: u64,
        rewrite_decision_changes: u64,
        rewrite_sat_unsat_conflicts: u64,
        query_slice_changed_instances: u64,
        query_slice_dropped_terms: u64,
        query_original_dag_nodes: u64,
        query_slice_dag_nodes: u64,
        query_original_tree_nodes: u64,
        query_slice_tree_nodes: u64,
        oracle_compared: u64,
        oracle_agree: u64,
        oracle_disagree: u64,
        oracle_skipped: u64,
        par2_seconds: f64,
        // Corpus layer attribution over decided pure-Rust (`sat-bv`) instances
        // only, so gate (a) — "does SAT solve time dominate?" — is falsifiable
        // from one summary. Other backends are excluded (their stage breakdown
        // is not the pure-Rust pipeline the CDCL gate is about). The four stages
        // are non-overlapping and sum to the pipeline wall time (`translate`
        // equals `bit_blast + cnf_encode` for this path, so it is not a separate
        // slice).
        layer_files: u64,
        layer_bit_blast_s: f64,
        layer_cnf_encode_s: f64,
        layer_solve_s: f64,
        layer_model_lift_s: f64,
    }

    struct InstanceRun {
        index: usize,
        record: JsonValue,
        summary: Summary,
    }

    pub fn main() -> ExitCode {
        let args = match parse_args() {
            Ok(a) => a,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };
        let files = collect_smt2(&args.dir, args.limit);
        if files.is_empty() {
            eprintln!("no .smt2 files under {}", args.dir.display());
            return ExitCode::FAILURE;
        }
        let timeout = Duration::from_millis(args.timeout_ms);
        let mut summary = Summary::default();
        let mut instances = Vec::new();
        let backend_name = make_backend(args.backend).capabilities().name;
        let compare_backend_name =
            make_compare_backend(args.compare_z3).map(|backend| backend.capabilities().name);
        let corpus_hash = fingerprint_corpus(&files, &args.dir);
        let config_hash = fingerprint_config(&args, &backend_name, &corpus_hash);

        let mut runs = match run_instances(&files, timeout, &args) {
            Ok(runs) => runs,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };
        runs.sort_by_key(|run| run.index);
        for run in runs {
            merge_summary(&mut summary, &run.summary);
            instances.push(run.record);
        }

        let artifact = match render_artifact(
            &args,
            &summary,
            &instances,
            &backend_name,
            compare_backend_name.as_deref(),
            &corpus_hash,
            &config_hash,
        ) {
            Ok(a) => a,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };
        if let Some(out) = &args.out {
            if let Err(e) = fs::write(out, &artifact) {
                eprintln!("write {}: {e}", out.display());
                return ExitCode::FAILURE;
            }
        } else {
            println!("{artifact}");
        }
        eprintln!(
            "files={} sat={} unsat={} unknown={} unsupported={} errors={} \
             agree={} DISAGREE={} model_replay_failures={} \
             rewrite_changed={} rewrite_apps={} rewrite_decision_changes={} \
             rewrite_sat_unsat_conflicts={} query_sliced={} query_dropped={} \
             par2_mean_s={:.3}",
            summary.files,
            summary.sat,
            summary.unsat,
            summary.unknown,
            summary.unsupported,
            summary.errors,
            summary.agree,
            summary.disagree,
            summary.model_replay_failures,
            summary.rewrite_changed_instances,
            summary.rewrite_applications,
            summary.rewrite_decision_changes,
            summary.rewrite_sat_unsat_conflicts,
            summary.query_slice_changed_instances,
            summary.query_slice_dropped_terms,
            summary.par2_seconds / decided_denominator(&summary)
        );
        if summary.disagree > 0 {
            eprintln!("SOUNDNESS ALARM: results disagree with benchmark :status ground truth");
            return ExitCode::FAILURE;
        }
        if summary.model_replay_failures > 0 {
            eprintln!("SOUNDNESS ALARM: sat model replay failed");
            return ExitCode::FAILURE;
        }
        if summary.rewrite_sat_unsat_conflicts > 0 {
            eprintln!("SOUNDNESS ALARM: rewrite changed a sat/unsat oracle decision");
            return ExitCode::FAILURE;
        }
        if summary.oracle_disagree > 0 {
            eprintln!("SOUNDNESS ALARM: primary backend disagrees with Z3 oracle");
            return ExitCode::FAILURE;
        }
        ExitCode::SUCCESS
    }

    /// Per-worker stack size. SMT-LIB terms can nest thousands deep, and the
    /// recursive parse/lower/eval traversals consume a frame per level; the
    /// default thread stack (≈2 MB on rayon workers, 8 MB on the main thread)
    /// overflows on such files and *aborts the whole batch* (a stack overflow
    /// cannot be caught). A large stack is reserved address space, not committed
    /// memory, so this costs nothing until the depth is actually reached.
    const WORKER_STACK_BYTES: usize = 512 * 1024 * 1024;

    fn run_instances(
        files: &[PathBuf],
        timeout: Duration,
        args: &Args,
    ) -> Result<Vec<InstanceRun>, String> {
        // Always run on a pool with a large stack (including `--jobs 1`, a
        // one-thread pool), so a single deeply-nested instance cannot crash the
        // run. `par_iter().collect()` preserves input order.
        rayon::ThreadPoolBuilder::new()
            .num_threads(args.jobs)
            .stack_size(WORKER_STACK_BYTES)
            .build()
            .map_err(|e| format!("create rayon thread pool: {e}"))
            .map(|pool| {
                pool.install(|| {
                    files
                        .par_iter()
                        .enumerate()
                        .map(|(index, file)| run_one_isolated(index, file, timeout, args))
                        .collect()
                })
            })
    }

    fn run_one_isolated(index: usize, file: &Path, timeout: Duration, args: &Args) -> InstanceRun {
        let mut summary = Summary {
            files: 1,
            ..Summary::default()
        };
        let mut backend = make_backend(args.backend);
        let mut compare_backend = make_compare_backend(args.compare_z3);
        let record = run_one(
            backend.as_mut(),
            &mut compare_backend,
            file,
            timeout,
            args,
            &mut summary,
        );
        InstanceRun {
            index,
            record,
            summary,
        }
    }

    fn make_backend(kind: BackendKind) -> Box<dyn SolverBackend> {
        match kind {
            BackendKind::SatBv => Box::new(SatBvBackend::new()),
            #[cfg(feature = "z3")]
            BackendKind::Z3 => Box::new(Z3Backend::new()),
        }
    }

    #[cfg(feature = "z3")]
    fn make_compare_backend(compare_z3: bool) -> Option<Box<dyn SolverBackend>> {
        compare_z3.then(|| Box::new(Z3Backend::new()) as Box<dyn SolverBackend>)
    }

    #[cfg(not(feature = "z3"))]
    fn make_compare_backend(_compare_z3: bool) -> Option<Box<dyn SolverBackend>> {
        None
    }

    fn decided_denominator(s: &Summary) -> f64 {
        #[allow(clippy::cast_precision_loss)]
        let n = (s.sat + s.unsat + s.unknown + s.errors).max(1) as f64;
        n
    }

    /// The `rewrite` sub-block of the summary artifact.
    fn rewrite_summary_record(s: &Summary, args: &Args) -> JsonValue {
        json!({
            "mode": args.rewrite.as_str(),
            "changed_instances": s.rewrite_changed_instances,
            "applications": s.rewrite_applications,
            "input_dag_nodes": s.rewrite_input_dag_nodes,
            "output_dag_nodes": s.rewrite_output_dag_nodes,
            "input_tree_nodes": s.rewrite_input_tree_nodes,
            "output_tree_nodes": s.rewrite_output_tree_nodes,
            "decision_matches": s.rewrite_decision_matches,
            "decision_changes": s.rewrite_decision_changes,
            "sat_unsat_conflicts": s.rewrite_sat_unsat_conflicts,
        })
    }

    /// Corpus layer attribution: per-stage seconds, each stage's share of the
    /// pure-Rust pipeline wall time, and the gate (a) verdict on whether SAT
    /// solve time dominates. `null` when no `sat-bv` instance was decided (the
    /// breakdown would be vacuous and a fabricated `0` share could be misread as
    /// "SAT does not dominate").
    fn layer_attribution_record(s: &Summary) -> JsonValue {
        if s.layer_files == 0 {
            return JsonValue::Null;
        }
        let total =
            s.layer_bit_blast_s + s.layer_cnf_encode_s + s.layer_solve_s + s.layer_model_lift_s;
        let share = |stage: f64| if total > 0.0 { stage / total } else { 0.0 };
        let sat_share = share(s.layer_solve_s);
        json!({
            "instances": s.layer_files,
            "total_pipeline_s": total,
            "bit_blast_s": s.layer_bit_blast_s,
            "cnf_encode_s": s.layer_cnf_encode_s,
            "solve_s": s.layer_solve_s,
            "model_lift_s": s.layer_model_lift_s,
            "bit_blast_share": share(s.layer_bit_blast_s),
            "cnf_encode_share": share(s.layer_cnf_encode_s),
            "solve_share": sat_share,
            "model_lift_share": share(s.layer_model_lift_s),
            // Gate (a): does SAT solve time dominate end-to-end? The CDCL-core
            // priority gate needs this and a CaDiCaL/Kissat gap before it jumps
            // the queue ahead of encoding work.
            "sat_dominates": sat_share > SAT_DOMINATES_SHARE,
            "sat_dominates_threshold": SAT_DOMINATES_SHARE,
        })
    }

    /// Runs one instance and returns its JSON record.
    fn run_one(
        backend: &mut dyn SolverBackend,
        compare_backend: &mut Option<Box<dyn SolverBackend>>,
        file: &Path,
        timeout: Duration,
        args: &Args,
        summary: &mut Summary,
    ) -> JsonValue {
        let name = file.display().to_string();
        let mut script = match read_script(file, &name, timeout, summary) {
            Ok(script) => script,
            Err(record) => return record,
        };
        let input_shape = TermStats::compute(&script.arena, &script.assertions);
        let mut rewrite = apply_rewrite(&mut script, args.rewrite);
        // Word-level preprocessing (P1.2): shrink the post-rewrite assertions and
        // keep a reconstruction trail so the sat model still replays against the
        // original query. The reduced set replaces what the backend solves.
        let preprocess_trail = if args.preprocess {
            let (reduced, trail) = apply_preprocess(&mut script.arena, &rewrite.assertions);
            rewrite.assertions = reduced;
            Some(trail)
        } else {
            None
        };
        let output_shape = TermStats::compute(&script.arena, &rewrite.assertions);
        accumulate_rewrite(summary, args.rewrite, &rewrite, &input_shape, &output_shape);
        let config = solver_config(args, timeout);
        let plan_config = PlanSolveConfig::from_args(args);
        let original_solve = if args.rewrite == RewriteMode::Default {
            Some(solve_planned(
                backend,
                &script.arena,
                &script.assertions,
                &script.assertions,
                &config,
                plan_config,
                None,
            ))
        } else {
            None
        };
        let primary_solve = solve_planned(
            backend,
            &script.arena,
            &rewrite.assertions,
            &script.assertions,
            &config,
            plan_config,
            preprocess_trail.as_ref(),
        );
        if let Some(original) = &original_solve {
            compare_rewrite_decision(&original.solve, &primary_solve.solve, summary);
        }
        let oracle_record = compare_backend.as_deref_mut().map(|backend| {
            compare_with_oracle(
                backend,
                &script,
                &rewrite,
                &primary_solve.solve,
                &config,
                summary,
                preprocess_trail.as_ref(),
            )
        });
        accumulate_query_plan(summary, &primary_solve.plan);
        accumulate_primary(&primary_solve.solve, summary);
        accumulate_par2(summary, &primary_solve.solve, timeout);
        accumulate_layers(summary, &primary_solve.solve);
        accumulate_expected_agreement(summary, script.status.as_deref(), &primary_solve.solve);
        let stats = &primary_solve.solve.stats;
        let mut record = json!({
            "file": name,
            "outcome": primary_solve.solve.outcome,
            "expected": script.status.as_deref().unwrap_or("unknown"),
            "translate_ms": duration_ms(stats.translate),
            "solve_ms": duration_ms(stats.solve),
            "model_lift_ms": duration_ms(stats.model_lift),
            "backend_stats": backend_stats_record(stats),
            "dag_nodes": input_shape.dag_nodes,
            "tree_nodes": input_shape.tree_nodes,
            "max_depth": input_shape.max_depth,
            "distinct_symbols": input_shape.distinct_symbols,
            "assertions": usize_to_u64(script.assertions.len()),
            "query_plan": query_plan_record(
                &primary_solve.plan,
                args.query_plan,
                primary_solve.refinement.as_ref(),
            ),
            "rewrite": rewrite_record(
                args.rewrite,
                &rewrite,
                &input_shape,
                &output_shape,
                original_solve.as_ref().map(|solve| &solve.solve),
                &primary_solve.solve,
            ),
        });
        if let Some(oracle) = oracle_record
            && let JsonValue::Object(obj) = &mut record
        {
            obj.insert("oracle".to_owned(), oracle);
        }
        if let Some(detail) = &primary_solve.solve.detail
            && let JsonValue::Object(obj) = &mut record
        {
            obj.insert("detail".to_owned(), json!(detail));
        }
        record
    }

    fn solver_config(args: &Args, timeout: Duration) -> SolverConfig {
        SolverConfig {
            timeout: Some(timeout),
            node_budget: args.node_budget,
            cnf_variable_budget: args.cnf_variable_budget,
            cnf_clause_budget: args.cnf_clause_budget,
            cnf_inprocessing: args.cnf_inprocessing,
            ..SolverConfig::default()
        }
    }

    fn read_script(
        file: &Path,
        name: &str,
        timeout: Duration,
        summary: &mut Summary,
    ) -> Result<Script, JsonValue> {
        let text = match fs::read_to_string(file) {
            Ok(t) => t,
            Err(e) => {
                summary.errors += 1;
                summary.par2_seconds += 2.0 * timeout.as_secs_f64();
                return Err(json!({
                    "file": name,
                    "outcome": "read-error",
                    "detail": e.to_string(),
                }));
            }
        };
        match parse_script(&text) {
            Ok(s) => Ok(s),
            Err(SmtError::Unsupported(what)) => {
                summary.unsupported += 1;
                Err(json!({
                    "file": name,
                    "outcome": "unsupported",
                    "detail": what,
                }))
            }
            Err(SmtError::Ir(e)) => {
                summary.unsupported += 1;
                Err(json!({
                    "file": name,
                    "outcome": "unsupported",
                    "detail": e.to_string(),
                }))
            }
            Err(e) => {
                summary.errors += 1;
                Err(json!({
                    "file": name,
                    "outcome": "parse-error",
                    "detail": e.to_string(),
                }))
            }
        }
    }

    struct RewriteRun {
        assertions: Vec<axeyum_ir::TermId>,
        report: RewriteReport,
    }

    /// Runs the model-sound word-level passes (`propagate_values` then
    /// `solve_eqs`) on `assertions`, returning the reduced assertions and the
    /// composed reconstruction trail. Mutates the arena (builds substituted terms),
    /// so it runs in the per-instance setup phase, before the shared-`&arena` solve.
    fn apply_preprocess(
        arena: &mut TermArena,
        assertions: &[TermId],
    ) -> (Vec<TermId>, ModelReconstructionTrail) {
        let (after_values, mut trail) = propagate_values(arena, assertions)
            .expect("propagate_values preserves IR well-formedness")
            .into_parts();
        let (reduced, eq_trail) = solve_eqs(arena, &after_values)
            .expect("solve_eqs preserves IR well-formedness")
            .into_parts();
        trail.append(eq_trail);
        // Re-canonicalize after substitution: `solve_eqs` inlines `x := t` by raw
        // structural rebuild, reintroducing un-normalized operator trees (e.g. a
        // multiplier tree `a*(b*c)` substituted opposite `c*(a*b)`) that the
        // initial canonicalization never saw because the symbols were still
        // abstract. Canonicalizing again AC-normalizes them so commute-shaped
        // goals fold without bit-blasting. Mirrors `check_with_preprocessing`.
        let reduced = canonicalize_terms(arena, &reduced)
            .expect("post-solve canonicalize preserves IR well-formedness")
            .terms;
        (reduced, trail)
    }

    fn apply_rewrite(script: &mut Script, mode: RewriteMode) -> RewriteRun {
        match mode {
            RewriteMode::Off => RewriteRun {
                assertions: script.assertions.clone(),
                report: RewriteReport::default(),
            },
            RewriteMode::Default => {
                let outcome = canonicalize_terms(&mut script.arena, &script.assertions)
                    .expect("default rewrite preserves IR well-formedness");
                RewriteRun {
                    assertions: outcome.terms,
                    report: outcome.report,
                }
            }
        }
    }

    struct SolveRecord {
        outcome: &'static str,
        detail: Option<String>,
        stats: SolveStats,
        model_replay_failure: bool,
    }

    struct PlannedSolve {
        solve: SolveRecord,
        plan: QueryPlan,
        refinement: Option<RefinementRecord>,
    }

    #[derive(Debug, Clone)]
    struct RefinementRecord {
        rounds: u64,
        replay_failures: u64,
        adaptive_backoffs: u64,
        max_rounds: u64,
        target_terms: u64,
        stopped: &'static str,
    }

    struct RefinementState {
        target_terms: Vec<TermId>,
        total_stats: SolveStats,
        replay_failures: u64,
        max_rounds: usize,
        current_batch_size: usize,
        adaptive_batch: bool,
        select_mode: RefineSelectMode,
        adaptive_backoffs: u64,
        last_added_terms: Vec<TermId>,
        exact_targets: bool,
    }

    #[derive(Clone, Copy)]
    struct RefinementProblem<'a> {
        arena: &'a TermArena,
        planned_assertions: &'a [TermId],
        replay_assertions: &'a [TermId],
        config: &'a SolverConfig,
        query: &'a Query,
    }

    impl RefinementState {
        fn new(
            first_target: TermId,
            max_rounds: usize,
            batch_size: usize,
            adaptive_batch: bool,
            select_mode: RefineSelectMode,
            exact_targets: bool,
        ) -> Self {
            Self {
                target_terms: vec![first_target],
                total_stats: SolveStats::default(),
                replay_failures: 0,
                max_rounds,
                current_batch_size: batch_size,
                adaptive_batch,
                select_mode,
                adaptive_backoffs: 0,
                last_added_terms: Vec::new(),
                exact_targets,
            }
        }

        fn run_round(
            &mut self,
            backend: &mut dyn SolverBackend,
            problem: RefinementProblem<'_>,
            round: usize,
        ) -> Option<PlannedSolve> {
            let plan = if self.exact_targets {
                problem
                    .query
                    .slice_exact_targets(problem.arena, &self.target_terms)
            } else {
                problem
                    .query
                    .slice_for_targets(problem.arena, &self.target_terms)
            };
            let solver_assertions = plan.solver_terms().collect::<Vec<_>>();
            let result = backend.check(problem.arena, &solver_assertions, problem.config);
            let stats = backend.last_stats().cloned().unwrap_or_default();

            match result {
                Ok(CheckResult::Sat(model)) => {
                    merge_stats(&mut self.total_stats, &stats);
                    self.handle_sat_model(problem, plan, &model, round)
                }
                Ok(CheckResult::Unsat) => {
                    merge_stats(&mut self.total_stats, &stats);
                    Some(self.finish("unsat", None, false, plan, round, "unsat-subset"))
                }
                Ok(CheckResult::Unknown(reason)) => {
                    if reason.kind == UnknownKind::EncodingBudget
                        && round < self.max_rounds
                        && self.backoff_last_batch()
                    {
                        None
                    } else {
                        merge_stats(&mut self.total_stats, &stats);
                        Some(self.finish(
                            "unknown",
                            Some(format!("{:?}: {}", reason.kind, reason.detail)),
                            false,
                            plan,
                            round,
                            "unknown",
                        ))
                    }
                }
                Err(SolverError::Unsupported(detail)) => {
                    merge_stats(&mut self.total_stats, &stats);
                    Some(self.finish(
                        "unsupported",
                        Some(detail),
                        false,
                        plan,
                        round,
                        "unsupported",
                    ))
                }
                Err(error) => {
                    merge_stats(&mut self.total_stats, &stats);
                    Some(self.finish(
                        "solver-error",
                        Some(error.to_string()),
                        false,
                        plan,
                        round,
                        "error",
                    ))
                }
            }
        }

        fn handle_sat_model(
            &mut self,
            problem: RefinementProblem<'_>,
            plan: QueryPlan,
            model: &Model,
            round: usize,
        ) -> Option<PlannedSolve> {
            match failed_replay_batch(
                problem.arena,
                problem.planned_assertions,
                problem.replay_assertions,
                model,
                ReplaySelection {
                    current_targets: &self.target_terms,
                    batch_size: self.current_batch_size,
                    select_mode: self.select_mode,
                    query: problem.query,
                    exact_targets: self.exact_targets,
                },
            ) {
                Ok(()) => Some(self.finish("sat", None, false, plan, round, "replayed")),
                Err(failure) => self.handle_replay_failure(failure, plan, round),
            }
        }

        fn handle_replay_failure(
            &mut self,
            failure: ReplayFailureBatch,
            plan: QueryPlan,
            round: usize,
        ) -> Option<PlannedSolve> {
            self.replay_failures += 1;
            if failure.already_targeted {
                return Some(self.finish(
                    "model-replay-error",
                    Some(format!(
                        "replay-refine failed on already-targeted assertion: {}",
                        failure.first.detail
                    )),
                    true,
                    plan,
                    round,
                    "replay-cycle",
                ));
            }
            if round == self.max_rounds {
                return Some(self.finish(
                    "unknown",
                    Some(format!(
                        "Incomplete: replay-refine stopped after {round} rounds; {}",
                        failure.first.detail
                    )),
                    false,
                    plan,
                    round,
                    "max-rounds",
                ));
            }
            self.last_added_terms = failure.new_terms;
            self.target_terms
                .extend(self.last_added_terms.iter().copied());
            None
        }

        fn backoff_last_batch(&mut self) -> bool {
            if !self.adaptive_batch || self.last_added_terms.len() <= 1 {
                return false;
            }

            let base_len = self.target_terms.len() - self.last_added_terms.len();
            let reduced_len = (self.last_added_terms.len() / 2).max(1);
            let reduced_terms = self.last_added_terms[..reduced_len].to_vec();
            self.target_terms.truncate(base_len);
            self.target_terms.extend(reduced_terms.iter().copied());
            self.last_added_terms = reduced_terms;
            self.current_batch_size = self.current_batch_size.min(reduced_len).max(1);
            self.adaptive_backoffs = self.adaptive_backoffs.saturating_add(1);
            true
        }

        fn finish(
            &self,
            outcome: &'static str,
            detail: Option<String>,
            model_replay_failure: bool,
            plan: QueryPlan,
            round: usize,
            stopped: &'static str,
        ) -> PlannedSolve {
            finish_refinement(
                outcome,
                detail,
                model_replay_failure,
                self.total_stats.clone(),
                plan,
                refinement_record(
                    round,
                    self.replay_failures,
                    self.adaptive_backoffs,
                    self.max_rounds,
                    self.target_terms.len(),
                    stopped,
                ),
            )
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum ReplayFailurePolicy {
        SoundnessAlarm,
        DowngradeToUnknown,
    }

    fn replay_policy_for_plan(plan: &QueryPlan) -> ReplayFailurePolicy {
        if plan.is_sliced() {
            ReplayFailurePolicy::DowngradeToUnknown
        } else {
            ReplayFailurePolicy::SoundnessAlarm
        }
    }

    fn solve_one(
        backend: &mut dyn SolverBackend,
        arena: &axeyum_ir::TermArena,
        solver_assertions: &[axeyum_ir::TermId],
        replay_assertions: &[axeyum_ir::TermId],
        config: &SolverConfig,
        replay_failure_policy: ReplayFailurePolicy,
        reconstruct: Option<&ModelReconstructionTrail>,
    ) -> SolveRecord {
        let result = backend.check(arena, solver_assertions, config);
        let stats = backend.last_stats().cloned().unwrap_or_default();
        let (outcome, detail, model_replay_failure) = classify_result(
            result,
            arena,
            replay_assertions,
            replay_failure_policy,
            reconstruct,
        );
        SolveRecord {
            outcome,
            detail,
            stats,
            model_replay_failure,
        }
    }

    fn solve_planned(
        backend: &mut dyn SolverBackend,
        arena: &TermArena,
        planned_assertions: &[TermId],
        replay_assertions: &[TermId],
        config: &SolverConfig,
        plan_config: PlanSolveConfig,
        reconstruct: Option<&ModelReconstructionTrail>,
    ) -> PlannedSolve {
        if plan_config.uses_replay_refinement() {
            // `--preprocess` is rejected with replay-refinement at arg validation.
            debug_assert!(reconstruct.is_none());
            return solve_with_replay_refinement(
                backend,
                arena,
                planned_assertions,
                replay_assertions,
                config,
                plan_config,
            );
        }

        let plan = query_plan_for_assertions(arena, planned_assertions, plan_config.mode);
        let solver_assertions = plan.solver_terms().collect::<Vec<_>>();
        let solve = solve_one(
            backend,
            arena,
            &solver_assertions,
            replay_assertions,
            config,
            replay_policy_for_plan(&plan),
            reconstruct,
        );
        PlannedSolve {
            solve,
            plan,
            refinement: None,
        }
    }

    fn solve_with_replay_refinement(
        backend: &mut dyn SolverBackend,
        arena: &TermArena,
        planned_assertions: &[TermId],
        replay_assertions: &[TermId],
        config: &SolverConfig,
        plan_config: PlanSolveConfig,
    ) -> PlannedSolve {
        let query = query_for_assertions(arena, planned_assertions);
        if planned_assertions.is_empty() {
            let plan = query.plan_full(arena);
            return solve_static_plan(
                backend,
                arena,
                replay_assertions,
                config,
                plan,
                Some(RefinementRecord {
                    rounds: 1,
                    replay_failures: 0,
                    adaptive_backoffs: 0,
                    max_rounds: usize_to_u64(plan_config.refine_rounds),
                    target_terms: 0,
                    stopped: "empty-query",
                }),
            );
        }

        let max_rounds = plan_config.refine_rounds.max(1);
        let mut state = RefinementState::new(
            planned_assertions[0],
            max_rounds,
            plan_config.refine_batch,
            plan_config.refine_adaptive_batch,
            plan_config.refine_select,
            plan_config.exact_targets(),
        );
        let problem = RefinementProblem {
            arena,
            planned_assertions,
            replay_assertions,
            config,
            query: &query,
        };

        for round in 1..=max_rounds {
            if let Some(result) = state.run_round(backend, problem, round) {
                return result;
            }
        }

        unreachable!("replay-refine loop always returns from its final round")
    }

    fn solve_static_plan(
        backend: &mut dyn SolverBackend,
        arena: &TermArena,
        replay_assertions: &[TermId],
        config: &SolverConfig,
        plan: QueryPlan,
        refinement: Option<RefinementRecord>,
    ) -> PlannedSolve {
        let solver_assertions = plan.solver_terms().collect::<Vec<_>>();
        let solve = solve_one(
            backend,
            arena,
            &solver_assertions,
            replay_assertions,
            config,
            replay_policy_for_plan(&plan),
            None,
        );
        PlannedSolve {
            solve,
            plan,
            refinement,
        }
    }

    fn finish_refinement(
        outcome: &'static str,
        detail: Option<String>,
        model_replay_failure: bool,
        stats: SolveStats,
        plan: QueryPlan,
        refinement: RefinementRecord,
    ) -> PlannedSolve {
        PlannedSolve {
            solve: SolveRecord {
                outcome,
                detail,
                stats,
                model_replay_failure,
            },
            plan,
            refinement: Some(refinement),
        }
    }

    fn refinement_record(
        round: usize,
        replay_failures: u64,
        adaptive_backoffs: u64,
        max_rounds: usize,
        target_terms: usize,
        stopped: &'static str,
    ) -> RefinementRecord {
        RefinementRecord {
            rounds: usize_to_u64(round),
            replay_failures,
            adaptive_backoffs,
            max_rounds: usize_to_u64(max_rounds),
            target_terms: usize_to_u64(target_terms),
            stopped,
        }
    }

    struct ReplayFailureDetail {
        term: TermId,
        detail: String,
    }

    struct ReplayFailureBatch {
        first: ReplayFailureDetail,
        new_terms: Vec<TermId>,
        already_targeted: bool,
    }

    #[derive(Clone, Copy)]
    struct ReplaySelection<'a> {
        current_targets: &'a [TermId],
        batch_size: usize,
        select_mode: RefineSelectMode,
        query: &'a Query,
        exact_targets: bool,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    struct FailureScore {
        dag_nodes: u64,
        tree_nodes: u64,
        ite_count: u64,
        term_index: usize,
    }

    #[derive(Clone)]
    struct FailureCandidate {
        term: TermId,
        score: FailureScore,
    }

    fn failed_replay_batch(
        arena: &TermArena,
        planned_assertions: &[TermId],
        replay_assertions: &[TermId],
        model: &Model,
        selection: ReplaySelection<'_>,
    ) -> Result<(), ReplayFailureBatch> {
        debug_assert_eq!(
            planned_assertions.len(),
            replay_assertions.len(),
            "rewrite must preserve assertion arity for replay refinement"
        );
        let assignment = model.to_assignment();
        let current_target_set = selection
            .current_targets
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        let mut first = None;
        let mut new_terms = Vec::new();
        let mut candidates = Vec::new();
        let mut already_targeted = false;

        for (&target, &assertion) in planned_assertions.iter().zip(replay_assertions) {
            let detail = match eval(arena, assertion, &assignment) {
                Ok(Value::Bool(true)) => continue,
                Ok(other) => format!("assertion #{} evaluated to {other}", assertion.index()),
                Err(error) => error.to_string(),
            };
            let failure = ReplayFailureDetail {
                term: assertion,
                detail,
            };
            if first.is_none() {
                first = Some(ReplayFailureDetail {
                    term: failure.term,
                    detail: failure.detail.clone(),
                });
            }
            if current_target_set.contains(&target) {
                already_targeted = true;
                break;
            }
            match selection.select_mode {
                RefineSelectMode::First => {
                    if !new_terms.contains(&target) {
                        new_terms.push(target);
                    }
                    if new_terms.len() >= selection.batch_size {
                        break;
                    }
                }
                RefineSelectMode::SmallestDag
                | RefineSelectMode::SmallestPlanDag
                | RefineSelectMode::SmallestPlanGreedy => {
                    if !candidates
                        .iter()
                        .any(|candidate: &FailureCandidate| candidate.term == target)
                    {
                        candidates.push(FailureCandidate {
                            term: target,
                            score: failure_score(arena, target),
                        });
                    }
                }
            }
        }

        if let Some(first) = first {
            if selection.select_mode != RefineSelectMode::First {
                new_terms = select_scored_failures(arena, candidates, selection);
            }
            Err(ReplayFailureBatch {
                first,
                new_terms,
                already_targeted,
            })
        } else {
            Ok(())
        }
    }

    fn select_scored_failures(
        arena: &TermArena,
        mut candidates: Vec<FailureCandidate>,
        selection: ReplaySelection<'_>,
    ) -> Vec<TermId> {
        candidates.sort_by_key(|candidate| candidate.score);
        match selection.select_mode {
            RefineSelectMode::First | RefineSelectMode::SmallestDag => {}
            RefineSelectMode::SmallestPlanDag | RefineSelectMode::SmallestPlanGreedy => {
                let plan_score_limit = candidates
                    .len()
                    .min(PLAN_REFINE_SCORE_CANDIDATES.max(selection.batch_size));
                candidates.truncate(plan_score_limit);
                if selection.select_mode == RefineSelectMode::SmallestPlanGreedy {
                    return select_plan_greedy_failures(arena, candidates, selection);
                }
                for candidate in &mut candidates {
                    candidate.score = plan_failure_score(
                        arena,
                        selection.query,
                        selection.current_targets,
                        &[],
                        candidate.term,
                        selection.exact_targets,
                    );
                }
                candidates.sort_by_key(|candidate| candidate.score);
            }
        }
        candidates
            .into_iter()
            .take(selection.batch_size)
            .map(|candidate| candidate.term)
            .collect()
    }

    fn select_plan_greedy_failures(
        arena: &TermArena,
        mut candidates: Vec<FailureCandidate>,
        selection: ReplaySelection<'_>,
    ) -> Vec<TermId> {
        let mut selected = Vec::new();
        while selected.len() < selection.batch_size && !candidates.is_empty() {
            for candidate in &mut candidates {
                candidate.score = plan_failure_score(
                    arena,
                    selection.query,
                    selection.current_targets,
                    &selected,
                    candidate.term,
                    selection.exact_targets,
                );
            }
            candidates.sort_by_key(|candidate| candidate.score);
            selected.push(candidates.remove(0).term);
        }
        selected
    }

    fn failure_score(arena: &TermArena, term: TermId) -> FailureScore {
        let stats = TermStats::compute(arena, &[term]);
        FailureScore {
            dag_nodes: stats.dag_nodes,
            tree_nodes: stats.tree_nodes,
            ite_count: stats.ite_count,
            term_index: term.index(),
        }
    }

    fn exact_target_failure_score(
        arena: &TermArena,
        current_targets: &[TermId],
        selected_targets: &[TermId],
        term: TermId,
    ) -> FailureScore {
        let mut targets = current_targets.to_vec();
        for &selected in selected_targets {
            if !targets.contains(&selected) {
                targets.push(selected);
            }
        }
        if !targets.contains(&term) {
            targets.push(term);
        }
        let stats = TermStats::compute(arena, &targets);
        FailureScore {
            dag_nodes: stats.dag_nodes,
            tree_nodes: stats.tree_nodes,
            ite_count: stats.ite_count,
            term_index: term.index(),
        }
    }

    fn plan_failure_score(
        arena: &TermArena,
        query: &Query,
        current_targets: &[TermId],
        selected_targets: &[TermId],
        term: TermId,
        exact_targets: bool,
    ) -> FailureScore {
        if exact_targets {
            return exact_target_failure_score(arena, current_targets, selected_targets, term);
        }
        let mut targets = current_targets.to_vec();
        for &selected in selected_targets {
            if !targets.contains(&selected) {
                targets.push(selected);
            }
        }
        if !targets.contains(&term) {
            targets.push(term);
        }
        let plan = if exact_targets {
            query.slice_exact_targets(arena, &targets)
        } else {
            query.slice_for_targets(arena, &targets)
        };
        let solver_terms = plan.solver_terms().collect::<Vec<_>>();
        let stats = TermStats::compute(arena, &solver_terms);
        FailureScore {
            dag_nodes: plan.solver_cache_key().dag_nodes,
            tree_nodes: plan.solver_cache_key().tree_nodes,
            ite_count: stats.ite_count,
            term_index: term.index(),
        }
    }

    fn merge_stats(total: &mut SolveStats, next: &SolveStats) {
        total.translate += next.translate;
        total.solve += next.solve;
        total.model_lift += next.model_lift;
        total.terms_translated = total.terms_translated.saturating_add(next.terms_translated);
        total.assertion_count = next.assertion_count;

        for (name, value) in &next.backend {
            merge_backend_stat(&mut total.backend, name, *value);
        }
    }

    fn merge_backend_stat(stats: &mut Vec<(String, f64)>, name: &str, value: f64) {
        if let Some((_, existing)) = stats.iter_mut().find(|(key, _)| key == name) {
            if name.ends_with("_ms") {
                *existing += value;
            } else {
                *existing = existing.max(value);
            }
        } else {
            stats.push((name.to_owned(), value));
        }
    }

    fn classify_result(
        result: Result<CheckResult, SolverError>,
        arena: &axeyum_ir::TermArena,
        replay_assertions: &[axeyum_ir::TermId],
        replay_failure_policy: ReplayFailurePolicy,
        reconstruct: Option<&ModelReconstructionTrail>,
    ) -> (&'static str, Option<String>, bool) {
        match result {
            Ok(CheckResult::Sat(model)) => {
                match replay_model(arena, replay_assertions, &model, reconstruct) {
                    Ok(()) => ("sat", None, false),
                    Err(e) if replay_failure_policy == ReplayFailurePolicy::DowngradeToUnknown => (
                        "unknown",
                        Some(format!(
                            "Incomplete: sliced sat model did not replay original query: {e}"
                        )),
                        false,
                    ),
                    Err(e) => ("model-replay-error", Some(e), true),
                }
            }
            Ok(CheckResult::Unsat) => ("unsat", None, false),
            Ok(CheckResult::Unknown(r)) => (
                "unknown",
                Some(format!("{:?}: {}", r.kind, r.detail)),
                false,
            ),
            Err(SolverError::Unsupported(detail)) => ("unsupported", Some(detail), false),
            Err(e) => ("solver-error", Some(e.to_string()), false),
        }
    }

    fn accumulate_primary(record: &SolveRecord, summary: &mut Summary) {
        match record.outcome {
            "sat" => summary.sat += 1,
            "unsat" => summary.unsat += 1,
            "unknown" => summary.unknown += 1,
            "unsupported" => summary.unsupported += 1,
            "model-replay-error" => {
                summary.errors += 1;
                summary.model_replay_failures += 1;
            }
            _ => summary.errors += 1,
        }
        if record.model_replay_failure && record.outcome != "model-replay-error" {
            summary.model_replay_failures += 1;
        }
    }

    /// Rolls a decided pure-Rust instance into the corpus layer attribution.
    ///
    /// Only `sat`/`unsat` instances solved by the `sat-bv` backend contribute:
    /// [`BvLayerStats::from_solve_stats`] returns `None` for any other backend,
    /// so this never fabricates a stage breakdown for, e.g., the Z3 oracle. The
    /// `translate` stage comes straight from [`SolveStats`].
    fn accumulate_layers(summary: &mut Summary, record: &SolveRecord) {
        if !matches!(record.outcome, "sat" | "unsat") {
            return;
        }
        let Some(layers) = BvLayerStats::from_solve_stats(&record.stats) else {
            return;
        };
        summary.layer_files += 1;
        summary.layer_bit_blast_s += layers.bit_blast.as_secs_f64();
        summary.layer_cnf_encode_s += layers.cnf_encode.as_secs_f64();
        summary.layer_solve_s += layers.solve.as_secs_f64();
        summary.layer_model_lift_s += layers.model_lift.as_secs_f64();
    }

    fn accumulate_par2(summary: &mut Summary, record: &SolveRecord, timeout: Duration) {
        if matches!(record.outcome, "sat" | "unsat") {
            summary.par2_seconds += record.stats.translate.as_secs_f64()
                + record.stats.solve.as_secs_f64()
                + record.stats.model_lift.as_secs_f64();
        } else {
            summary.par2_seconds += 2.0 * timeout.as_secs_f64();
        }
    }

    fn accumulate_expected_agreement(
        summary: &mut Summary,
        expected: Option<&str>,
        record: &SolveRecord,
    ) {
        let Some(expected @ ("sat" | "unsat")) = expected else {
            return;
        };
        if !matches!(record.outcome, "sat" | "unsat") {
            return;
        }
        if expected == record.outcome {
            summary.agree += 1;
        } else {
            summary.disagree += 1;
        }
    }

    fn merge_summary(total: &mut Summary, next: &Summary) {
        total.files += next.files;
        total.unsupported += next.unsupported;
        total.sat += next.sat;
        total.unsat += next.unsat;
        total.unknown += next.unknown;
        total.errors += next.errors;
        total.agree += next.agree;
        total.disagree += next.disagree;
        total.model_replay_failures += next.model_replay_failures;
        total.rewrite_changed_instances += next.rewrite_changed_instances;
        total.rewrite_applications += next.rewrite_applications;
        total.rewrite_input_dag_nodes += next.rewrite_input_dag_nodes;
        total.rewrite_output_dag_nodes += next.rewrite_output_dag_nodes;
        total.rewrite_input_tree_nodes += next.rewrite_input_tree_nodes;
        total.rewrite_output_tree_nodes += next.rewrite_output_tree_nodes;
        total.rewrite_decision_matches += next.rewrite_decision_matches;
        total.rewrite_decision_changes += next.rewrite_decision_changes;
        total.rewrite_sat_unsat_conflicts += next.rewrite_sat_unsat_conflicts;
        total.query_slice_changed_instances += next.query_slice_changed_instances;
        total.query_slice_dropped_terms += next.query_slice_dropped_terms;
        total.query_original_dag_nodes += next.query_original_dag_nodes;
        total.query_slice_dag_nodes += next.query_slice_dag_nodes;
        total.query_original_tree_nodes += next.query_original_tree_nodes;
        total.query_slice_tree_nodes += next.query_slice_tree_nodes;
        total.oracle_compared += next.oracle_compared;
        total.oracle_agree += next.oracle_agree;
        total.oracle_disagree += next.oracle_disagree;
        total.oracle_skipped += next.oracle_skipped;
        total.par2_seconds += next.par2_seconds;
        total.layer_files += next.layer_files;
        total.layer_bit_blast_s += next.layer_bit_blast_s;
        total.layer_cnf_encode_s += next.layer_cnf_encode_s;
        total.layer_solve_s += next.layer_solve_s;
        total.layer_model_lift_s += next.layer_model_lift_s;
    }

    fn compare_with_oracle(
        oracle: &mut dyn SolverBackend,
        script: &Script,
        rewrite: &RewriteRun,
        primary: &SolveRecord,
        config: &SolverConfig,
        summary: &mut Summary,
        reconstruct: Option<&ModelReconstructionTrail>,
    ) -> JsonValue {
        if !matches!(primary.outcome, "sat" | "unsat") {
            summary.oracle_skipped += 1;
            return json!({
                "enabled": true,
                "backend_kind": "z3",
                "skipped": format!("primary-outcome-{}", primary.outcome),
            });
        }

        let oracle_config = SolverConfig {
            timeout: config.timeout,
            resource_limit: config.resource_limit,
            memory_limit_mb: config.memory_limit_mb,
            ..SolverConfig::default()
        };
        let oracle_solve = solve_one(
            oracle,
            &script.arena,
            &rewrite.assertions,
            &script.assertions,
            &oracle_config,
            ReplayFailurePolicy::SoundnessAlarm,
            reconstruct,
        );
        let compared = matches!(oracle_solve.outcome, "sat" | "unsat");
        let agrees = compared && oracle_solve.outcome == primary.outcome;
        if compared {
            summary.oracle_compared += 1;
            if agrees {
                summary.oracle_agree += 1;
            } else {
                summary.oracle_disagree += 1;
            }
        } else {
            summary.oracle_skipped += 1;
        }

        let mut record = json!({
            "enabled": true,
            "backend_kind": "z3",
            "outcome": oracle_solve.outcome,
            "decision_compared": compared,
            "decision_agrees": if compared { JsonValue::Bool(agrees) } else { JsonValue::Null },
            "translate_ms": duration_ms(oracle_solve.stats.translate),
            "solve_ms": duration_ms(oracle_solve.stats.solve),
            "model_lift_ms": duration_ms(oracle_solve.stats.model_lift),
            "backend_stats": backend_stats_record(&oracle_solve.stats),
        });
        if let Some(detail) = &oracle_solve.detail
            && let JsonValue::Object(obj) = &mut record
        {
            obj.insert("detail".to_owned(), json!(detail));
        }
        record
    }

    fn query_plan_for_assertions(
        arena: &TermArena,
        assertions: &[TermId],
        mode: QueryPlanMode,
    ) -> QueryPlan {
        let query = query_for_assertions(arena, assertions);
        match mode {
            QueryPlanMode::Full => query.plan_full(arena),
            QueryPlanMode::FirstAssertionSupport | QueryPlanMode::ReplayRefine => {
                if let Some(target) = assertions.first() {
                    query.slice_for_targets(arena, std::slice::from_ref(target))
                } else {
                    query.plan_full(arena)
                }
            }
            QueryPlanMode::ReplayRefineExact => {
                if let Some(target) = assertions.first() {
                    query.slice_exact_targets(arena, std::slice::from_ref(target))
                } else {
                    query.plan_full(arena)
                }
            }
        }
    }

    fn query_for_assertions(arena: &TermArena, assertions: &[TermId]) -> Query {
        let mut builder = Query::builder(arena);
        for &assertion in assertions {
            builder
                .assert(assertion)
                .expect("SMT-LIB parser only emits Boolean assertions");
        }
        builder.build()
    }

    fn accumulate_query_plan(summary: &mut Summary, plan: &QueryPlan) {
        if plan.is_sliced() {
            summary.query_slice_changed_instances += 1;
        }
        summary.query_slice_dropped_terms = summary
            .query_slice_dropped_terms
            .saturating_add(usize_to_u64(plan.dropped_terms().len()));
        summary.query_original_dag_nodes = summary
            .query_original_dag_nodes
            .saturating_add(plan.original_cache_key().dag_nodes);
        summary.query_slice_dag_nodes = summary
            .query_slice_dag_nodes
            .saturating_add(plan.solver_cache_key().dag_nodes);
        summary.query_original_tree_nodes = summary
            .query_original_tree_nodes
            .saturating_add(plan.original_cache_key().tree_nodes);
        summary.query_slice_tree_nodes = summary
            .query_slice_tree_nodes
            .saturating_add(plan.solver_cache_key().tree_nodes);
    }

    fn accumulate_rewrite(
        summary: &mut Summary,
        mode: RewriteMode,
        rewrite: &RewriteRun,
        input_shape: &TermStats,
        output_shape: &TermStats,
    ) {
        if mode == RewriteMode::Off {
            return;
        }
        if rewrite.report.changed() {
            summary.rewrite_changed_instances += 1;
        }
        summary.rewrite_applications += usize_to_u64(rewrite.report.applications().len());
        summary.rewrite_input_dag_nodes = summary
            .rewrite_input_dag_nodes
            .saturating_add(input_shape.dag_nodes);
        summary.rewrite_output_dag_nodes = summary
            .rewrite_output_dag_nodes
            .saturating_add(output_shape.dag_nodes);
        summary.rewrite_input_tree_nodes = summary
            .rewrite_input_tree_nodes
            .saturating_add(input_shape.tree_nodes);
        summary.rewrite_output_tree_nodes = summary
            .rewrite_output_tree_nodes
            .saturating_add(output_shape.tree_nodes);
    }

    fn compare_rewrite_decision(
        original: &SolveRecord,
        rewritten: &SolveRecord,
        summary: &mut Summary,
    ) {
        if original.outcome == rewritten.outcome {
            summary.rewrite_decision_matches += 1;
        } else {
            summary.rewrite_decision_changes += 1;
            if matches!(original.outcome, "sat" | "unsat")
                && matches!(rewritten.outcome, "sat" | "unsat")
            {
                summary.rewrite_sat_unsat_conflicts += 1;
            }
        }
    }

    fn replay_model(
        arena: &axeyum_ir::TermArena,
        assertions: &[axeyum_ir::TermId],
        model: &Model,
        reconstruct: Option<&ModelReconstructionTrail>,
    ) -> Result<(), String> {
        // With word-level preprocessing the backend's model is over the reduced
        // symbols; reconstruct the eliminated variables before replaying against
        // the original assertions.
        let assignment = match reconstruct {
            Some(trail) => trail
                .reconstruct(arena, &model.to_assignment())
                .map_err(|e| e.to_string())?,
            None => model.to_assignment(),
        };
        for &assertion in assertions {
            match eval(arena, assertion, &assignment) {
                Ok(Value::Bool(true)) => {}
                Ok(other) => {
                    return Err(format!(
                        "assertion #{} evaluated to {other}",
                        assertion.index()
                    ));
                }
                Err(e) => return Err(e.to_string()),
            }
        }
        Ok(())
    }

    fn render_artifact(
        args: &Args,
        s: &Summary,
        instances: &[JsonValue],
        backend_name: &str,
        compare_backend_name: Option<&str>,
        corpus_hash: &str,
        config_hash: &str,
    ) -> Result<String, String> {
        let limit = optional_limit(args.limit);
        let families = optional_strings(&args.families);
        let node_budget = args
            .node_budget
            .map_or(JsonValue::Null, |budget| json!(budget));
        let cnf_variable_budget = args
            .cnf_variable_budget
            .map_or(JsonValue::Null, |budget| json!(budget));
        let cnf_clause_budget = args
            .cnf_clause_budget
            .map_or(JsonValue::Null, |budget| json!(budget));
        let artifact = json!({
            "version": ARTIFACT_VERSION,
            "config": {
                "corpus": args.dir.display().to_string(),
                "corpus_source": args.corpus_source,
                "corpus_hash": corpus_hash,
                "config_hash": config_hash,
                "logic": args.logic,
                "selected_families": families,
                "timeout_ms": args.timeout_ms,
                "jobs": usize_to_u64(args.jobs),
                "node_budget": node_budget,
                "cnf_variable_budget": cnf_variable_budget,
                "cnf_clause_budget": cnf_clause_budget,
                "cnf_inprocessing": args.cnf_inprocessing,
                "preprocess": args.preprocess,
                "limit": limit,
                "backend": backend_name,
                "backend_kind": args.backend.as_str(),
                "compare_backend": compare_backend_name,
                "compare_z3": args.compare_z3,
                "query_plan": {
                    "mode": args.query_plan.as_str(),
                    "sat_replay_failure_policy": sat_replay_policy_name(args.query_plan),
                    "refine_rounds": usize_to_u64(args.refine_rounds),
                    "refine_batch": usize_to_u64(args.refine_batch),
                    "refine_adaptive_batch": args.refine_adaptive_batch,
                    "refine_select": args.refine_select.as_str(),
                },
                "harness": format!("axeyum-bench {}", env!("CARGO_PKG_VERSION")),
                "seed": args.seed,
                "rewrite": rewrite_config(args.rewrite),
                "hardware": hardware_note(),
            },
            "summary": {
                "files": s.files,
                "sat": s.sat,
                "unsat": s.unsat,
                "unknown": s.unknown,
                "unsupported": s.unsupported,
                "errors": s.errors,
                "agree": s.agree,
                "disagree": s.disagree,
                "model_replay_failures": s.model_replay_failures,
                "par2_mean_s": s.par2_seconds / decided_denominator(s),
                "rewrite": rewrite_summary_record(s, args),
                "query_plan": {
                    "slice_changed_instances": s.query_slice_changed_instances,
                    "slice_dropped_terms": s.query_slice_dropped_terms,
                    "original_dag_nodes": s.query_original_dag_nodes,
                    "slice_dag_nodes": s.query_slice_dag_nodes,
                    "original_tree_nodes": s.query_original_tree_nodes,
                    "slice_tree_nodes": s.query_slice_tree_nodes,
                },
                "oracle": {
                    "enabled": args.compare_z3,
                    "backend": compare_backend_name,
                    "compared": s.oracle_compared,
                    "agree": s.oracle_agree,
                    "disagree": s.oracle_disagree,
                    "skipped": s.oracle_skipped,
                },
                "layer_attribution": layer_attribution_record(s),
            },
            "triage": {
                "unsupported": triage(instances, &["unsupported"]),
                "errors": triage(
                    instances,
                    &["read-error", "parse-error", "solver-error", "model-replay-error"]
                ),
                "rewrite_decision_changes": rewrite_decision_changes(instances),
                "soundness": {
                    "status_disagreements": s.disagree,
                    "model_replay_failures": s.model_replay_failures,
                    "rewrite_sat_unsat_conflicts": s.rewrite_sat_unsat_conflicts,
                    "oracle_disagreements": s.oracle_disagree,
                },
            },
            "instances": instances,
        });
        serde_json::to_string_pretty(&artifact).map_err(|e| format!("render artifact: {e}"))
    }

    fn query_plan_record(
        plan: &QueryPlan,
        mode: QueryPlanMode,
        refinement: Option<&RefinementRecord>,
    ) -> JsonValue {
        let mut record = json!({
            "cache_key": cache_key_record(plan.original_cache_key()),
            "submitted": {
                "strategy": mode.as_str(),
                "target_support_symbols": usize_to_u64(plan.target_support().len()),
                "sliced": plan.is_sliced(),
                "planned_terms": usize_to_u64(plan.planned_terms().len()),
                "dropped_terms": usize_to_u64(plan.dropped_terms().len()),
                "solver_cache_key": cache_key_record(plan.solver_cache_key()),
            },
        });
        if let Some(refinement) = refinement
            && let JsonValue::Object(obj) = &mut record
        {
            obj.insert(
                "refinement".to_owned(),
                json!({
                    "rounds": refinement.rounds,
                    "replay_failures": refinement.replay_failures,
                    "adaptive_backoffs": refinement.adaptive_backoffs,
                    "max_rounds": refinement.max_rounds,
                    "target_terms": refinement.target_terms,
                    "stopped": refinement.stopped,
                }),
            );
        }
        record
    }

    fn sat_replay_policy_name(mode: QueryPlanMode) -> &'static str {
        match mode {
            QueryPlanMode::Full => "soundness-alarm",
            QueryPlanMode::FirstAssertionSupport => "downgrade-to-unknown",
            QueryPlanMode::ReplayRefine | QueryPlanMode::ReplayRefineExact => {
                "refine-before-unknown"
            }
        }
    }

    fn cache_key_record(key: &StructuralCacheKey) -> JsonValue {
        json!({
            "digest": key.hex(),
            "assertions": key.assertions,
            "assumptions": key.assumptions,
            "dag_nodes": key.dag_nodes,
            "tree_nodes": key.tree_nodes,
        })
    }

    fn rewrite_config(mode: RewriteMode) -> JsonValue {
        let rule_ids = if mode == RewriteMode::Default {
            default_manifest()
                .enabled_rules()
                .map(|rule| rule.id.as_str().to_owned())
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        json!({
            "mode": mode.as_str(),
            "rule_set": if mode == RewriteMode::Default {
                JsonValue::String("axeyum-rewrite-default-v1".to_owned())
            } else {
                JsonValue::Null
            },
            "enabled_rule_ids": rule_ids,
        })
    }

    fn rewrite_record(
        mode: RewriteMode,
        rewrite: &RewriteRun,
        input_shape: &TermStats,
        output_shape: &TermStats,
        original_solve: Option<&SolveRecord>,
        primary_solve: &SolveRecord,
    ) -> JsonValue {
        let rule_counts = rule_counts(&rewrite.report);
        let original_outcome = original_solve.map_or(JsonValue::Null, |solve| json!(solve.outcome));
        let original_detail = original_solve
            .and_then(|solve| solve.detail.as_ref())
            .map_or(JsonValue::Null, |detail| json!(detail));
        let decision_changed = original_solve
            .map(|solve| solve.outcome != primary_solve.outcome)
            .map_or(JsonValue::Null, |changed| json!(changed));
        json!({
            "mode": mode.as_str(),
            "changed": rewrite.report.changed(),
            "applications": usize_to_u64(rewrite.report.applications().len()),
            "rule_counts": rule_counts,
            "input_dag_nodes": input_shape.dag_nodes,
            "output_dag_nodes": output_shape.dag_nodes,
            "input_tree_nodes": input_shape.tree_nodes,
            "output_tree_nodes": output_shape.tree_nodes,
            "output_max_depth": output_shape.max_depth,
            "output_distinct_symbols": output_shape.distinct_symbols,
            "output_assertions": usize_to_u64(rewrite.assertions.len()),
            "original_outcome": original_outcome,
            "original_detail": original_detail,
            "rewritten_outcome": primary_solve.outcome,
            "decision_changed": decision_changed,
        })
    }

    fn rule_counts(report: &RewriteReport) -> BTreeMap<String, u64> {
        let mut counts = BTreeMap::new();
        for application in report.applications() {
            *counts
                .entry(application.rule_id.as_str().to_owned())
                .or_insert(0) += 1;
        }
        counts
    }

    fn optional_limit(limit: usize) -> JsonValue {
        if limit == usize::MAX {
            JsonValue::Null
        } else {
            json!(usize_to_u64(limit))
        }
    }

    fn optional_strings(values: &[String]) -> JsonValue {
        if values.is_empty() {
            JsonValue::Null
        } else {
            json!(values)
        }
    }

    fn triage(instances: &[JsonValue], outcomes: &[&str]) -> Vec<JsonValue> {
        instances
            .iter()
            .filter_map(|instance| {
                let outcome = instance.get("outcome")?.as_str()?;
                if !outcomes.contains(&outcome) {
                    return None;
                }
                Some(json!({
                    "file": instance.get("file").cloned().unwrap_or(JsonValue::Null),
                    "outcome": outcome,
                    "detail": instance.get("detail").cloned().unwrap_or(JsonValue::Null),
                }))
            })
            .collect()
    }

    fn rewrite_decision_changes(instances: &[JsonValue]) -> Vec<JsonValue> {
        instances
            .iter()
            .filter_map(|instance| {
                let rewrite = instance.get("rewrite")?;
                let changed = rewrite.get("decision_changed")?.as_bool()?;
                if !changed {
                    return None;
                }
                Some(json!({
                    "file": instance.get("file").cloned().unwrap_or(JsonValue::Null),
                    "original_outcome": rewrite
                        .get("original_outcome")
                        .cloned()
                        .unwrap_or(JsonValue::Null),
                    "rewritten_outcome": rewrite
                        .get("rewritten_outcome")
                        .cloned()
                        .unwrap_or(JsonValue::Null),
                    "original_detail": rewrite
                        .get("original_detail")
                        .cloned()
                        .unwrap_or(JsonValue::Null),
                    "rewritten_detail": instance.get("detail").cloned().unwrap_or(JsonValue::Null),
                }))
            })
            .collect()
    }

    fn duration_ms(duration: Duration) -> u64 {
        u64::try_from(duration.as_millis()).unwrap_or(u64::MAX)
    }

    fn backend_stats_record(stats: &SolveStats) -> JsonValue {
        let mut values = BTreeMap::new();
        for (name, value) in &stats.backend {
            values.insert(name.clone(), *value);
        }
        json!(values)
    }

    fn usize_to_u64(n: usize) -> u64 {
        u64::try_from(n).unwrap_or(u64::MAX)
    }

    fn hardware_note() -> JsonValue {
        let parallelism = std::thread::available_parallelism().map_or(1, std::num::NonZero::get);
        json!({
            "os": std::env::consts::OS,
            "arch": std::env::consts::ARCH,
            "parallelism": usize_to_u64(parallelism),
            "hostname": std::env::var("HOSTNAME").ok(),
        })
    }

    fn fingerprint_config(args: &Args, backend_name: &str, corpus_hash: &str) -> String {
        let mut hash = FNV_OFFSET;
        update_hash(&mut hash, args.dir.display().to_string().as_bytes());
        update_hash(&mut hash, &args.timeout_ms.to_le_bytes());
        update_hash(&mut hash, &usize_to_u64(args.jobs).to_le_bytes());
        update_hash(&mut hash, &usize_to_u64(args.limit).to_le_bytes());
        update_hash(
            &mut hash,
            args.corpus_source.as_deref().unwrap_or("").as_bytes(),
        );
        update_hash(&mut hash, args.logic.as_deref().unwrap_or("").as_bytes());
        for family in &args.families {
            update_hash(&mut hash, family.as_bytes());
            update_hash(&mut hash, &[0]);
        }
        update_hash(&mut hash, args.seed.as_bytes());
        update_hash(&mut hash, args.rewrite.as_str().as_bytes());
        update_hash(&mut hash, args.backend.as_str().as_bytes());
        update_hash(&mut hash, args.query_plan.as_str().as_bytes());
        update_hash(&mut hash, &usize_to_u64(args.refine_rounds).to_le_bytes());
        update_hash(&mut hash, &usize_to_u64(args.refine_batch).to_le_bytes());
        update_hash(&mut hash, &[u8::from(args.refine_adaptive_batch)]);
        update_hash(&mut hash, args.refine_select.as_str().as_bytes());
        update_hash(
            &mut hash,
            &args.node_budget.unwrap_or(u64::MAX).to_le_bytes(),
        );
        update_hash(
            &mut hash,
            &args.cnf_variable_budget.unwrap_or(u64::MAX).to_le_bytes(),
        );
        update_hash(
            &mut hash,
            &args.cnf_clause_budget.unwrap_or(u64::MAX).to_le_bytes(),
        );
        update_hash(&mut hash, &[u8::from(args.cnf_inprocessing)]);
        update_hash(&mut hash, &[u8::from(args.preprocess)]);
        update_hash(&mut hash, &[u8::from(args.compare_z3)]);
        update_hash(&mut hash, backend_name.as_bytes());
        update_hash(&mut hash, corpus_hash.as_bytes());
        hex_u64(hash)
    }

    fn fingerprint_corpus(files: &[PathBuf], root: &Path) -> String {
        let mut hash = FNV_OFFSET;
        for file in files {
            let relative = file.strip_prefix(root).unwrap_or(file);
            update_hash(&mut hash, relative.to_string_lossy().as_bytes());
            update_hash(&mut hash, &[0]);
            match fs::read(file) {
                Ok(bytes) => update_hash(&mut hash, &bytes),
                Err(e) => update_hash(&mut hash, format!("read-error:{e}").as_bytes()),
            }
            update_hash(&mut hash, &[0xff]);
        }
        hex_u64(hash)
    }

    fn update_hash(hash: &mut u64, bytes: &[u8]) {
        for b in bytes {
            *hash ^= u64::from(*b);
            *hash = hash.wrapping_mul(FNV_PRIME);
        }
    }

    fn hex_u64(hash: u64) -> String {
        format!("{hash:016x}")
    }

    fn collect_smt2(dir: &Path, limit: usize) -> Vec<PathBuf> {
        let mut files = Vec::new();
        let mut dirs = vec![dir.to_path_buf()];
        while let Some(d) = dirs.pop() {
            let Ok(entries) = std::fs::read_dir(&d) else {
                continue;
            };
            for e in entries.flatten() {
                let p = e.path();
                if p.is_dir() {
                    dirs.push(p);
                } else if p.extension().is_some_and(|x| x == "smt2") {
                    files.push(p);
                }
            }
        }
        // Deterministic order regardless of filesystem iteration.
        files.sort();
        files.truncate(limit);
        files
    }

    #[cfg(test)]
    mod tests {
        use axeyum_ir::{Sort, Value};

        use super::*;

        #[test]
        fn replay_refinement_adds_rewritten_target_for_original_replay_failure() {
            let mut arena = TermArena::new();
            let p_symbol = arena.declare("p", Sort::Bool).unwrap();
            let q_symbol = arena.declare("q", Sort::Bool).unwrap();
            let p = arena.var(p_symbol);
            let q = arena.var(q_symbol);
            let original_assertion = arena.and(p, q).unwrap();
            let rewritten_assertion = p;
            let query = query_for_assertions(&arena, &[rewritten_assertion]);
            let mut model = Model::new();
            model.set(p_symbol, Value::Bool(false));
            model.set(q_symbol, Value::Bool(true));

            let failure = failed_replay_batch(
                &arena,
                &[rewritten_assertion],
                &[original_assertion],
                &model,
                ReplaySelection {
                    current_targets: &[],
                    batch_size: 1,
                    select_mode: RefineSelectMode::First,
                    query: &query,
                    exact_targets: true,
                },
            )
            .unwrap_err();

            assert_eq!(failure.first.term, original_assertion);
            assert_eq!(failure.new_terms, vec![rewritten_assertion]);
            assert!(!failure.already_targeted);
        }

        #[test]
        fn greedy_plan_selector_rescores_after_each_selected_failure() {
            let mut arena = TermArena::new();
            let current = arena.bool_var("current").unwrap();
            let alpha = arena.bool_var("a").unwrap();
            let beta = arena.bool_var("b").unwrap();
            let gamma = arena.bool_var("c").unwrap();
            let delta = arena.bool_var("d").unwrap();
            let epsilon = arena.bool_var("e").unwrap();
            let phi = arena.bool_var("f").unwrap();
            let eta = arena.bool_var("g").unwrap();

            let shared_small = arena.and(alpha, beta).unwrap();
            let reused_inner = arena.and(shared_small, gamma).unwrap();
            let reused_large = arena.and(reused_inner, eta).unwrap();
            let independent_inner = arena.and(delta, epsilon).unwrap();
            let independent = arena.and(independent_inner, phi).unwrap();
            let assertions = [current, shared_small, independent, reused_large];
            let query = query_for_assertions(&arena, &assertions);
            let candidates = [shared_small, independent, reused_large]
                .into_iter()
                .map(|term| FailureCandidate {
                    term,
                    score: failure_score(&arena, term),
                })
                .collect::<Vec<_>>();

            let static_plan_selection = select_scored_failures(
                &arena,
                candidates.clone(),
                ReplaySelection {
                    current_targets: &[current],
                    batch_size: 2,
                    select_mode: RefineSelectMode::SmallestPlanDag,
                    query: &query,
                    exact_targets: true,
                },
            );
            assert_eq!(static_plan_selection, vec![shared_small, independent]);

            let greedy_selection = select_scored_failures(
                &arena,
                candidates,
                ReplaySelection {
                    current_targets: &[current],
                    batch_size: 2,
                    select_mode: RefineSelectMode::SmallestPlanGreedy,
                    query: &query,
                    exact_targets: true,
                },
            );
            assert_eq!(greedy_selection, vec![shared_small, reused_large]);
        }
    }
}
