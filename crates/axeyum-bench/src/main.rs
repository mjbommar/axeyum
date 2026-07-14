//! Benchmark harness (benchmarking-and-performance-methodology note).
//!
//! Walks a corpus directory of `.smt2` files, runs each through the solver
//! trait, and emits a versioned JSON results artifact: per-instance result,
//! ground-truth agreement, layer-attributed timing, and PAR-2 scoring.
//! Disagreement with a benchmark's `:status` is a soundness alarm and makes
//! the run exit nonzero.
//!
//! Usage: `axeyum-bench <dir> [--timeout-ms N] [--limit N] [--out FILE]`
//!   `[--corpus-source TEXT] [--corpus-manifest FILE] [--corpus-tier NAME]`
//!   `[--generate-corpus-manifest CAPTURE_INDEX]`
//!   `[--logic LOGIC] [--families CSV]`
//!   `[--rewrite off|default] [--backend sat-bv|z3]`
//!   `[--query-plan full|first-assertion-support|replay-refine|replay-refine-exact]`
//!   `[--refine-rounds N] [--refine-batch N] [--refine-adaptive-batch]`
//!   `[--refine-select first|smallest-dag|smallest-plan-dag|smallest-plan-greedy]`
//!   `[--resource-limit N] [--node-budget N] [--cnf-var-budget N]`
//!   `[--cnf-clause-budget N] [--require-deterministic-resources]`
//!   `[--prove-unsat]`
//!   `[--require-reproducible-run]`
//!   `[--compare-z3] [--require-in-process-z3] [--min-decided-percent P] [--jobs N]`
//! The default build can run the pure Rust `sat-bv` backend. Build with
//! `--features z3` (or `z3-static`) to enable the Z3 oracle backend.

fn main() -> std::process::ExitCode {
    run::main()
}

mod run {
    use std::collections::{BTreeMap, BTreeSet};
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Command, ExitCode};
    use std::time::{Duration, Instant};

    use axeyum_cnf::rustsat_batsat_determinism;
    use axeyum_ir::{Op, TermArena, TermId, TermNode, TermStats, Value, eval};
    use axeyum_query::{Query, QueryPlan, StructuralCacheKey};
    use axeyum_rewrite::{
        DEFAULT_SOLVE_EQS_FUEL, ModelReconstructionTrail, RewriteReport, canonicalize_terms,
        default_manifest, propagate_values, solve_eqs_bounded,
    };
    use axeyum_smtlib::{Script, ScriptCommand, SmtError, parse_script};
    use axeyum_solver::{
        BvLayerStats, Capabilities, CheckResult, LazyBvBackend, Model, SatBvBackend, SolveStats,
        SolverBackend, SolverConfig, SolverError, UnknownKind, check_model_with_assignment, solve,
    };
    #[cfg(feature = "z3")]
    use axeyum_solver::{DETERMINISTIC_Z3_RANDOM_SEED, Z3Backend};
    use rayon::prelude::*;
    use serde_json::{Value as JsonValue, json};
    use sha2::{Digest, Sha256};

    const ARTIFACT_VERSION: u32 = 22;
    const CORPUS_MANIFEST_VERSION: u64 = 1;
    const CONTENT_HASH_PREFIX: &str = "sha256:";
    const DETERMINISM_PROFILE: &str = "axeyum-bench-fixed-seeds-v1";
    const RESOURCE_PROFILE: &str = "axeyum-qfbv-cold-bounded-v1";
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
        /// P2.1 lazy abstraction-refinement (CEGAR) bit-blasting (ADR-0019).
        LazyBv,
        /// Lazy bit-blasting that also abstracts `ite` (P2.1 lever #3).
        LazyBvIte,
        /// The unified division-general front door
        /// ([`axeyum_solver::solve`]) — the actual product path that routes
        /// `QF_LRA`→LRA, `QF_UF`→EUF, `QF_LIA`→LIA, `QF_NRA`/`QF_NIA`, `QF_ABV`,
        /// `QF_DT`, … and quantified queries (`forall`/`exists`) to the
        /// quantifier solver, so every division can be measured head-to-head
        /// against Z3. (Quantifier-free queries delegate to `check_auto`
        /// unchanged.)
        Solver,
        #[cfg(feature = "z3")]
        Z3,
    }

    impl BackendKind {
        fn as_str(self) -> &'static str {
            match self {
                BackendKind::SatBv => "sat-bv",
                BackendKind::LazyBv => "lazy-bv",
                BackendKind::LazyBvIte => "lazy-bv-ite",
                BackendKind::Solver => "solver",
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
        corpus_manifest: Option<PathBuf>,
        corpus_tier: Option<String>,
        generate_corpus_manifest: Option<PathBuf>,
        logic: Option<String>,
        families: Vec<String>,
        rewrite: RewriteMode,
        backend: BackendKind,
        query_plan: QueryPlanMode,
        refine_rounds: usize,
        refine_batch: usize,
        refine_adaptive_batch: bool,
        refine_select: RefineSelectMode,
        resource_limit: Option<u64>,
        node_budget: Option<u64>,
        cnf_variable_budget: Option<u64>,
        cnf_clause_budget: Option<u64>,
        cnf_inprocessing: bool,
        cnf_vivify: bool,
        native_cdcl: bool,
        prove_unsat: bool,
        preprocess: bool,
        compare_z3: bool,
        require_in_process_z3: bool,
        require_reproducible_run: bool,
        require_deterministic_resources: bool,
        min_decided_percent: Option<f64>,
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
            corpus_manifest: None,
            corpus_tier: None,
            generate_corpus_manifest: None,
            logic: None,
            families: Vec::new(),
            rewrite: RewriteMode::Off,
            backend: default_backend_kind(),
            query_plan: QueryPlanMode::Full,
            refine_rounds: DEFAULT_REFINE_ROUNDS,
            refine_batch: 1,
            refine_adaptive_batch: false,
            refine_select: RefineSelectMode::First,
            resource_limit: None,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            cnf_inprocessing: false,
            cnf_vivify: false,
            native_cdcl: false,
            prove_unsat: false,
            preprocess: false,
            compare_z3: false,
            require_in_process_z3: false,
            require_reproducible_run: false,
            require_deterministic_resources: false,
            min_decided_percent: None,
            jobs: 1,
        };
        while let Some(flag) = args.next() {
            parse_option(&mut parsed, &flag, &mut args)?;
        }
        validate_args(&parsed)?;
        Ok(parsed)
    }

    #[allow(clippy::too_many_lines)]
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
            "--corpus-manifest" => {
                parsed.corpus_manifest = Some(PathBuf::from(next_value(args, flag)?));
            }
            "--corpus-tier" => parsed.corpus_tier = Some(next_value(args, flag)?),
            "--generate-corpus-manifest" => {
                parsed.generate_corpus_manifest = Some(PathBuf::from(next_value(args, flag)?));
            }
            "--logic" => parsed.logic = Some(next_value(args, flag)?),
            "--families" => {
                parsed.families = next_value(args, flag)?
                    .split(',')
                    .map(str::trim)
                    .filter(|family| !family.is_empty())
                    .map(ToOwned::to_owned)
                    .collect();
            }
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
            "--resource-limit" => {
                parsed.resource_limit = Some(
                    next_value(args, flag)?
                        .parse()
                        .map_err(|e| format!("{e}"))?,
                );
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
            "--vivify" => parsed.cnf_vivify = true,
            "--native-cdcl" => parsed.native_cdcl = true,
            "--prove-unsat" => parsed.prove_unsat = true,
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
            "--require-in-process-z3" => {
                #[cfg(feature = "z3")]
                {
                    parsed.require_in_process_z3 = true;
                }
                #[cfg(not(feature = "z3"))]
                {
                    return Err(
                        "`--require-in-process-z3` requires building axeyum-bench with \
                         --features z3"
                            .to_owned(),
                    );
                }
            }
            "--require-reproducible-run" => parsed.require_reproducible_run = true,
            "--require-deterministic-resources" => {
                parsed.require_deterministic_resources = true;
            }
            "--min-decided-percent" => {
                parsed.min_decided_percent = Some(parse_decided_percent(&next_value(args, flag)?)?);
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

    fn parse_decided_percent(value: &str) -> Result<f64, String> {
        let percent = value.parse::<f64>().map_err(|error| error.to_string())?;
        if !percent.is_finite() || !(0.0..=100.0).contains(&percent) {
            return Err("`--min-decided-percent` must be between 0 and 100".to_owned());
        }
        Ok(percent)
    }

    fn next_value(args: &mut impl Iterator<Item = String>, flag: &str) -> Result<String, String> {
        args.next().ok_or(format!("missing value for {flag}"))
    }

    fn validate_args(args: &Args) -> Result<(), String> {
        if args.generate_corpus_manifest.is_some() {
            if args.out.is_none() {
                return Err("`--generate-corpus-manifest` requires `--out`".to_owned());
            }
            if args.corpus_manifest.is_some() || args.corpus_tier.is_some() {
                return Err(
                    "`--generate-corpus-manifest` cannot be combined with `--corpus-manifest` or `--corpus-tier`"
                        .to_owned(),
                );
            }
            if args.limit != usize::MAX {
                return Err(
                    "`--generate-corpus-manifest` cannot be combined with `--limit`; capture indexes must cover the exact corpus"
                        .to_owned(),
                );
            }
        }
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
        if args.require_in_process_z3 && !args.compare_z3 {
            return Err("`--require-in-process-z3` requires `--compare-z3`".to_owned());
        }
        if args.prove_unsat && !matches!(args.backend, BackendKind::SatBv) {
            return Err("`--prove-unsat` requires `--backend sat-bv`".to_owned());
        }
        if args.require_deterministic_resources {
            if !matches!(args.backend, BackendKind::SatBv) {
                return Err(
                    "`--require-deterministic-resources` currently requires `--backend sat-bv`"
                        .to_owned(),
                );
            }
            let missing = missing_deterministic_resource_limits(
                args.resource_limit,
                args.node_budget,
                args.cnf_variable_budget,
                args.cnf_clause_budget,
            );
            if !missing.is_empty() {
                return Err(format!(
                    "`--require-deterministic-resources` requires positive {}",
                    missing.join(", ")
                ));
            }
        }
        if args.corpus_tier.is_some() && args.corpus_manifest.is_none() {
            return Err("`--corpus-tier` requires `--corpus-manifest`".to_owned());
        }
        if args.corpus_manifest.is_some() && args.limit != usize::MAX {
            return Err(
                "`--limit` cannot be combined with `--corpus-manifest`; use a named manifest tier"
                    .to_owned(),
            );
        }
        Ok(())
    }

    fn missing_deterministic_resource_limits(
        resource_limit: Option<u64>,
        node_budget: Option<u64>,
        cnf_variable_budget: Option<u64>,
        cnf_clause_budget: Option<u64>,
    ) -> Vec<&'static str> {
        [
            ("--resource-limit", resource_limit),
            ("--node-budget", node_budget),
            ("--cnf-var-budget", cnf_variable_budget),
            ("--cnf-clause-budget", cnf_clause_budget),
        ]
        .into_iter()
        .filter_map(|(name, value)| value.is_none_or(|limit| limit == 0).then_some(name))
        .collect()
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
            "lazy-bv" => Ok(BackendKind::LazyBv),
            "lazy-bv-ite" => Ok(BackendKind::LazyBvIte),
            "solver" | "auto" => Ok(BackendKind::Solver),
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

    #[derive(Debug, Clone, Copy)]
    struct LayerSample {
        word_preprocess: f64,
        bit_blast: f64,
        cnf_encode: f64,
        cnf_inprocess: f64,
        solve: f64,
        model_lift: f64,
        model_replay: f64,
        aig_inputs: u64,
        aig_nodes: u64,
        cnf_variables: u64,
        cnf_clauses: u64,
    }

    /// Original-query structural profile used to verify that an external `QF_BV`
    /// tier actually has the binary-lifter shape it claims to represent. Counts
    /// are over unique reachable DAG nodes, so parser-preserved sharing cannot
    /// inflate an operator family by repeated tree expansion.
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    struct QueryShapeSample {
        dag_nodes: u64,
        tree_nodes: u64,
        max_depth: u64,
        distinct_symbols: u64,
        assertions: u64,
        bitvec_nodes: u64,
        distinct_bitvec_widths: u64,
        max_bitvec_width: u64,
        extracts: u64,
        extract_result_bits: u64,
        extract_source_bits: u64,
        narrow_extracts: u64,
        concats: u64,
        zero_exts: u64,
        sign_exts: u64,
        selects: u64,
        stores: u64,
        extract_over_concat: u64,
        extract_over_extract: u64,
        extract_over_zero_ext: u64,
        extract_over_sign_ext: u64,
        low_extract_over_zero_ext: u64,
    }

    impl QueryShapeSample {
        fn compute(arena: &TermArena, roots: &[TermId], base: &TermStats) -> Self {
            let mut sample = Self {
                dag_nodes: base.dag_nodes,
                tree_nodes: base.tree_nodes,
                max_depth: base.max_depth,
                distinct_symbols: base.distinct_symbols,
                assertions: usize_to_u64(roots.len()),
                ..Self::default()
            };
            let mut seen = BTreeSet::new();
            let mut widths = BTreeSet::new();
            let mut stack = roots.to_vec();
            while let Some(term) = stack.pop() {
                if !seen.insert(term) {
                    continue;
                }
                if let Some(width) = arena.sort_of(term).bv_width() {
                    sample.bitvec_nodes += 1;
                    sample.max_bitvec_width = sample.max_bitvec_width.max(u64::from(width));
                    widths.insert(width);
                }
                let TermNode::App { op, args } = arena.node(term) else {
                    continue;
                };
                stack.extend(args.iter().copied());
                match *op {
                    Op::Extract { hi, lo } => {
                        sample.extracts += 1;
                        sample.extract_result_bits += u64::from(hi - lo + 1);
                        let source_width = arena.sort_of(args[0]).bv_width().unwrap_or(0);
                        sample.extract_source_bits += u64::from(source_width);
                        sample.narrow_extracts += u64::from(hi - lo + 1 < source_width);
                        if let TermNode::App {
                            op: child_op,
                            args: child_args,
                        } = arena.node(args[0])
                        {
                            match child_op {
                                Op::Concat => sample.extract_over_concat += 1,
                                Op::Extract { .. } => sample.extract_over_extract += 1,
                                Op::ZeroExt { .. } => {
                                    sample.extract_over_zero_ext += 1;
                                    let original_width =
                                        arena.sort_of(child_args[0]).bv_width().unwrap_or(0);
                                    sample.low_extract_over_zero_ext +=
                                        u64::from(lo == 0 && hi + 1 == original_width);
                                }
                                Op::SignExt { .. } => sample.extract_over_sign_ext += 1,
                                _ => {}
                            }
                        }
                    }
                    Op::Concat => sample.concats += 1,
                    Op::ZeroExt { .. } => sample.zero_exts += 1,
                    Op::SignExt { .. } => sample.sign_exts += 1,
                    Op::Select => sample.selects += 1,
                    Op::Store => sample.stores += 1,
                    _ => {}
                }
            }
            sample.distinct_bitvec_widths = usize_to_u64(widths.len());
            sample
        }

        fn cancellation_opportunities(self) -> u64 {
            self.extract_over_concat
                + self.extract_over_extract
                + self.extract_over_zero_ext
                + self.extract_over_sign_ext
        }
    }

    impl LayerSample {
        fn total_s(self) -> f64 {
            self.word_preprocess
                + self.bit_blast
                + self.cnf_encode
                + self.cnf_inprocess
                + self.solve
                + self.model_lift
                + self.model_replay
        }
    }

    #[derive(Debug, Clone, Copy)]
    struct ClientComparisonSample {
        axeyum_s: f64,
        z3_s: f64,
    }

    /// One immutable query identity in a versioned external-corpus manifest.
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct CorpusManifestEntry {
        path: String,
        content_hash: String,
        expected: String,
        family: String,
        tiers: Vec<String>,
    }

    /// Validated manifest metadata plus the entries selected for this run.
    #[derive(Debug)]
    struct CorpusManifestSelection {
        manifest_path: PathBuf,
        manifest_hash: String,
        name: String,
        source: String,
        logic: String,
        total_entries: usize,
        selected_tier: Option<String>,
        entries: Vec<CorpusManifestEntry>,
    }

    /// The exact ordered set of files a run is allowed to consume.
    struct CorpusSelection {
        files: Vec<PathBuf>,
        manifest: Option<CorpusManifestSelection>,
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
        unsat_proof_replay_checked: u64,
        unsat_proof_replay_missing: u64,
        unsat_proof_replay_s: f64,
        unsat_proof_replay_sample: Option<f64>,
        unsat_proof_replay_samples: Vec<f64>,
        /// Root-cause "leaderboard of blockers": for every non-decided instance
        /// (`unknown`/`unsupported`/error), a count keyed by the precise reason —
        /// `unknown:Timeout`, `unknown:EncodingBudget`, `unknown:NodeBudget`,
        /// `unknown:ResourceLimit`, `unknown:Incomplete`, `unsupported`,
        /// `solver-error`, `model-replay-error`, … — so a run says *why* the
        /// undecided instances were not solved, not just how many. Deterministic
        /// (`BTreeMap` key order).
        blocker_buckets: BTreeMap<String, u64>,
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
        // is not the pure-Rust pipeline the CDCL gate is about). The six stages
        // are non-overlapping and sum to the cold pipeline wall time. Word-level
        // preprocessing runs in the harness before the backend; `translate`
        // equals bit-blast + CNF encode + optional CNF inprocessing for this path.
        layer_files: u64,
        layer_word_preprocess_s: f64,
        layer_bit_blast_s: f64,
        layer_cnf_encode_s: f64,
        layer_cnf_inprocess_s: f64,
        layer_solve_s: f64,
        layer_model_lift_s: f64,
        layer_model_replay_s: f64,
        layer_model_replay_files: u64,
        /// One fixed-size sample on per-file summaries; the merged corpus keeps
        /// the samples in one allocation for exact deterministic p50/p95 values.
        layer_sample: Option<LayerSample>,
        layer_samples: Vec<LayerSample>,
        /// Structural samples from the untouched parsed assertions. Unlike
        /// layer samples these include every successfully parsed flat query,
        /// regardless of verdict, so a fast failure cannot erase evidence that
        /// the selected corpus has (or lacks) the target lifter shape.
        query_shape_files: u64,
        query_shape_sample: Option<QueryShapeSample>,
        query_shape_samples: Vec<QueryShapeSample>,
        /// Fair in-process comparison over the original query: Axeyum includes
        /// its selected word preprocessing, while Z3 receives the untouched
        /// parsed assertions. Binary-fallback timings are deliberately excluded.
        client_comparison_files: u64,
        client_axeyum_s: f64,
        client_z3_s: f64,
        client_comparison_sample: Option<ClientComparisonSample>,
        client_comparison_samples: Vec<ClientComparisonSample>,
        /// Expected-verdict gate supplied by a versioned corpus manifest. This is
        /// deliberately separate from optional SMT-LIB `:status` metadata.
        manifest_expected: u64,
        manifest_compared: u64,
        manifest_agree: u64,
        manifest_disagree: u64,
    }

    struct InstanceRun {
        index: usize,
        record: JsonValue,
        summary: Summary,
    }

    struct ArtifactIdentity<'a> {
        backend_name: &'a str,
        compare_backend_name: Option<&'a str>,
        corpus_hash: &'a str,
        config_hash: &'a str,
        corpus_manifest: Option<&'a CorpusManifestSelection>,
        experiment: &'a ExperimentIdentity,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct HardwareIdentity {
        os: String,
        arch: String,
        parallelism: u64,
        cpu_model: Option<String>,
        kernel: Option<String>,
        total_memory_bytes: Option<u64>,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct ExperimentIdentity {
        source_revision: Option<String>,
        source_dirty: Option<bool>,
        cargo_lock_hash: Option<String>,
        rustc: Option<String>,
        cargo: Option<String>,
        build_profile: String,
        backend: String,
        compare_backend: Option<String>,
        hardware: HardwareIdentity,
        environment_hash: String,
    }

    pub fn main() -> ExitCode {
        let args = match parse_args() {
            Ok(a) => a,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };
        if let Some(index_path) = &args.generate_corpus_manifest {
            let out = args
                .out
                .as_deref()
                .expect("generation mode was validated to require --out");
            return match generate_corpus_manifest(&args.dir, index_path, out) {
                Ok(()) => ExitCode::SUCCESS,
                Err(error) => {
                    eprintln!("{error}");
                    ExitCode::FAILURE
                }
            };
        }
        let corpus = match load_corpus(&args) {
            Ok(corpus) => corpus,
            Err(error) => {
                eprintln!("{error}");
                return ExitCode::FAILURE;
            }
        };
        if corpus.files.is_empty() {
            eprintln!("no .smt2 files under {}", args.dir.display());
            return ExitCode::FAILURE;
        }
        let timeout = Duration::from_millis(args.timeout_ms);
        let mut summary = Summary::default();
        let mut instances = Vec::new();
        let backend_name = make_backend(args.backend).capabilities().name;
        let compare_backend_name =
            make_compare_backend(args.compare_z3).map(|backend| backend.capabilities().name);
        let experiment =
            ExperimentIdentity::collect(&backend_name, compare_backend_name.as_deref());
        if args.require_reproducible_run
            && let Err(error) = experiment.require_reproducible()
        {
            eprintln!("{error}");
            return ExitCode::FAILURE;
        }
        let corpus_hash = fingerprint_corpus(&corpus.files, &args.dir);
        let config_hash =
            fingerprint_config(&args, &backend_name, &corpus_hash, corpus.manifest.as_ref());

        let mut runs = match run_instances(&corpus.files, timeout, &args) {
            Ok(runs) => runs,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };
        runs.sort_by_key(|run| run.index);
        for mut run in runs {
            merge_summary(&mut summary, &run.summary);
            if let Some(manifest) = &corpus.manifest {
                annotate_manifest_result(
                    &mut run.record,
                    &manifest.entries[run.index],
                    &mut summary,
                );
            }
            instances.push(run.record);
        }

        let identity = ArtifactIdentity {
            backend_name: &backend_name,
            compare_backend_name: compare_backend_name.as_deref(),
            corpus_hash: &corpus_hash,
            config_hash: &config_hash,
            corpus_manifest: corpus.manifest.as_ref(),
            experiment: &experiment,
        };
        let artifact = match render_artifact(&args, &summary, &instances, &identity) {
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
        report_summary(
            &summary,
            args.min_decided_percent,
            args.require_in_process_z3,
        )
    }

    /// Prints the one-line corpus summary + the root-cause blocker leaderboard, then
    /// returns the process exit code — `FAILURE` (after a printed `SOUNDNESS ALARM`)
    /// if any soundness invariant tripped (oracle/ground-truth disagreement, a sat
    /// model that did not replay, a rewrite that flipped a decision), else `SUCCESS`.
    fn report_summary(
        summary: &Summary,
        min_decided_percent: Option<f64>,
        require_in_process_z3: bool,
    ) -> ExitCode {
        eprintln!(
            "files={} sat={} unsat={} unknown={} unsupported={} errors={} \
             agree={} DISAGREE={} model_replay_failures={} \
             proof_replay_checked={} proof_replay_missing={} \
             manifest_agree={} MANIFEST_DISAGREE={} \
             rewrite_changed={} rewrite_apps={} rewrite_decision_changes={} \
             rewrite_sat_unsat_conflicts={} query_sliced={} query_dropped={} \
             decided_percent={:.2} par2_mean_s={:.3}",
            summary.files,
            summary.sat,
            summary.unsat,
            summary.unknown,
            summary.unsupported,
            summary.errors,
            summary.agree,
            summary.disagree,
            summary.model_replay_failures,
            summary.unsat_proof_replay_checked,
            summary.unsat_proof_replay_missing,
            summary.manifest_agree,
            summary.manifest_disagree,
            summary.rewrite_changed_instances,
            summary.rewrite_applications,
            summary.rewrite_decision_changes,
            summary.rewrite_sat_unsat_conflicts,
            summary.query_slice_changed_instances,
            summary.query_slice_dropped_terms,
            decided_percent(summary),
            summary.par2_seconds / decided_denominator(summary)
        );
        if !summary.blocker_buckets.is_empty() {
            eprintln!(
                "blockers: {}",
                blocker_leaderboard(&summary.blocker_buckets)
            );
        }
        if summary.disagree > 0 {
            eprintln!("SOUNDNESS ALARM: results disagree with benchmark :status ground truth");
            return ExitCode::FAILURE;
        }
        if summary.model_replay_failures > 0 {
            eprintln!("SOUNDNESS ALARM: sat model replay failed");
            return ExitCode::FAILURE;
        }
        if summary.unsat_proof_replay_missing > 0 {
            eprintln!("SOUNDNESS ALARM: requested unsat proof replay was not checked");
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
        if summary.errors > 0 {
            eprintln!(
                "BENCHMARK INTEGRITY ALARM: {} operational errors cannot count as fast results",
                summary.errors
            );
            return ExitCode::FAILURE;
        }
        if summary.manifest_expected > 0
            && (summary.manifest_compared != summary.manifest_expected
                || summary.manifest_disagree > 0)
        {
            eprintln!(
                "BENCHMARK INTEGRITY ALARM: manifest compared {}/{} expected verdicts with {} disagreements",
                summary.manifest_compared, summary.manifest_expected, summary.manifest_disagree
            );
            return ExitCode::FAILURE;
        }
        if let Some(required) = min_decided_percent
            && decided_percent(summary) + f64::EPSILON < required
        {
            eprintln!(
                "BENCHMARK INTEGRITY ALARM: decided {:.2}% is below required {:.2}%",
                decided_percent(summary),
                required
            );
            return ExitCode::FAILURE;
        }
        if require_in_process_z3 && summary.client_comparison_files != summary.files {
            eprintln!(
                "BENCHMARK INTEGRITY ALARM: in-process Z3 compared {} of {} files",
                summary.client_comparison_files, summary.files
            );
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
            BackendKind::LazyBv => Box::new(LazyBvBackend::new()),
            BackendKind::LazyBvIte => Box::new(LazyBvBackend::new().with_abstract_ite(true)),
            BackendKind::Solver => Box::new(CheckAutoBackend::new()),
            #[cfg(feature = "z3")]
            BackendKind::Z3 => Box::new(Z3Backend::new()),
        }
    }

    /// A [`SolverBackend`] adapter over the unified division-general front door
    /// [`axeyum_solver::solve`] — the actual product path that routes a parsed
    /// benchmark to its theory engine (`QF_LRA`→LRA, `QF_UF`→EUF, `QF_LIA`→LIA,
    /// `QF_NRA`/`QF_NIA`, `QF_ABV`, `QF_DT`, …) and routes quantified
    /// (`forall`/`exists`) queries to the quantifier solver. It exists so every
    /// division — quantifier-free and quantified — can be
    /// measured head-to-head against Z3 through the *same* result/timing/PAR-2/`--compare-z3`
    /// plumbing the BV backends use; the only difference is how the verdict is
    /// obtained. For quantifier-free queries `solve` delegates to `check_auto`,
    /// so the quantifier-free behavior is unchanged.
    ///
    /// `solve` takes `&mut TermArena` (its preprocessing/elimination passes
    /// build new terms), but the [`SolverBackend::check`] contract hands an
    /// immutable `&TermArena` shared across the rayon workers. We therefore solve
    /// against a per-call **clone** of the arena. This is sound for downstream model
    /// replay: `TermArena::clone` preserves the [`TermId`]s of the original terms
    /// (it only ever *appends* new ones), and a [`Model`] keys on global
    /// `SymbolId`/`FuncId`s — never clone-local ids — so the returned model replays
    /// verbatim against the original arena the harness evaluates with.
    struct CheckAutoBackend {
        stats: Option<SolveStats>,
    }

    impl CheckAutoBackend {
        fn new() -> Self {
            Self { stats: None }
        }
    }

    impl SolverBackend for CheckAutoBackend {
        fn capabilities(&self) -> Capabilities {
            Capabilities {
                name: "axeyum-solver solve".to_owned(),
                produces_models: true,
                // `solve` returns a first-class `unknown` on the
                // undecidable/unimplemented frontier; it is not a complete decider
                // for every fragment it accepts.
                complete: false,
            }
        }

        fn check(
            &mut self,
            arena: &TermArena,
            assertions: &[TermId],
            config: &SolverConfig,
        ) -> Result<CheckResult, SolverError> {
            // Solve against a mutable clone; see the type doc for why this is sound
            // for model replay against the caller's original arena.
            let mut owned = arena.clone();
            let start = Instant::now();
            // `solve` (and the `check_auto` it delegates to for QF queries) is
            // reached through engines that still panic (rather than
            // returning a first-class `unknown`) on a few corners of their accepted
            // fragment — a measurement harness must not let one such instance abort
            // the whole rayon batch and lose every other verdict. Isolate the call:
            // a panic becomes a per-instance `Unsupported` (recorded as
            // `unsupported`, never a fabricated `sat`/`unsat`), so the run stays
            // soundness-clean and completes. `owned`, `assertions`, and `config` are
            // not observed after a panic (the clone is dropped), so asserting
            // unwind-safety is correct.
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                solve(&mut owned, assertions, config)
            }))
            .unwrap_or_else(|_| {
                Err(SolverError::Unsupported(
                    "solve panicked on this instance (engine-internal); recorded \
                     as unsupported rather than crashing the batch or fabricating a verdict"
                        .to_owned(),
                ))
            });
            let elapsed = start.elapsed();
            let mut stats = SolveStats::default();
            stats.solve = elapsed;
            stats.assertion_count = usize_to_u64(assertions.len());
            // Surface wall time as a backend stat too, mirroring how the other
            // backends populate `backend` so `backend_stats_record` is non-empty.
            stats
                .backend
                .push(("solve_ms".to_owned(), elapsed.as_secs_f64() * 1000.0));
            self.stats = Some(stats);
            result
        }

        fn last_stats(&self) -> Option<&SolveStats> {
            self.stats.as_ref()
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

    #[allow(clippy::cast_precision_loss)]
    fn decided_percent(s: &Summary) -> f64 {
        if s.files == 0 {
            0.0
        } else {
            100.0 * (s.sat + s.unsat) as f64 / s.files as f64
        }
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

    #[allow(clippy::cast_precision_loss)]
    fn timing_distribution_record<T: Copy>(
        samples: &[T],
        select_seconds: impl Fn(T) -> f64,
    ) -> JsonValue {
        if samples.is_empty() {
            return JsonValue::Null;
        }
        let mut values = samples
            .iter()
            .copied()
            .map(select_seconds)
            .collect::<Vec<_>>();
        values.sort_by(f64::total_cmp);
        let percentile = |percent: usize| {
            let rank = percent
                .saturating_mul(values.len())
                .div_ceil(100)
                .saturating_sub(1);
            values[rank.min(values.len() - 1)] * 1000.0
        };
        let mean_ms = values.iter().sum::<f64>() * 1000.0 / values.len() as f64;
        json!({
            "min_ms": values[0] * 1000.0,
            "p50_ms": percentile(50),
            "p95_ms": percentile(95),
            "max_ms": values[values.len() - 1] * 1000.0,
            "mean_ms": mean_ms,
        })
    }

    #[allow(clippy::cast_precision_loss)]
    fn count_distribution_record<T: Copy>(samples: &[T], select: impl Fn(T) -> u64) -> JsonValue {
        if samples.is_empty() {
            return JsonValue::Null;
        }
        let mut values = samples.iter().copied().map(select).collect::<Vec<_>>();
        values.sort_unstable();
        let percentile = |percent: usize| {
            let rank = percent
                .saturating_mul(values.len())
                .div_ceil(100)
                .saturating_sub(1);
            values[rank.min(values.len() - 1)]
        };
        let total = values
            .iter()
            .fold(0_u128, |sum, &value| sum + u128::from(value));
        json!({
            "min": values[0],
            "p50": percentile(50),
            "p95": percentile(95),
            "max": values[values.len() - 1],
            "mean": total as f64 / values.len() as f64,
        })
    }

    fn sum_shape(samples: &[QueryShapeSample], select: impl Fn(QueryShapeSample) -> u64) -> u64 {
        samples
            .iter()
            .copied()
            .map(select)
            .fold(0, u64::saturating_add)
    }

    fn query_shape_record(sample: QueryShapeSample) -> JsonValue {
        json!({
            "counting_unit": "unique original-query DAG nodes",
            "formula": {
                "assertions": sample.assertions,
                "dag_nodes": sample.dag_nodes,
                "tree_nodes": sample.tree_nodes,
                "max_depth": sample.max_depth,
                "distinct_symbols": sample.distinct_symbols,
            },
            "widths": {
                "bitvec_nodes": sample.bitvec_nodes,
                "distinct_bitvec_widths": sample.distinct_bitvec_widths,
                "max_bitvec_width": sample.max_bitvec_width,
            },
            "operators": {
                "extract": sample.extracts,
                "concat": sample.concats,
                "zero_extend": sample.zero_exts,
                "sign_extend": sample.sign_exts,
                "select": sample.selects,
                "store": sample.stores,
            },
            "extract_demand": {
                "result_bits": sample.extract_result_bits,
                "source_bits": sample.extract_source_bits,
                "narrow_extracts": sample.narrow_extracts,
            },
            "coercion_cancellation_opportunities": {
                "total": sample.cancellation_opportunities(),
                "extract_over_concat": sample.extract_over_concat,
                "extract_over_extract": sample.extract_over_extract,
                "extract_over_zero_extend": sample.extract_over_zero_ext,
                "extract_over_sign_extend": sample.extract_over_sign_ext,
                "exact_low_extract_over_zero_extend": sample.low_extract_over_zero_ext,
            },
        })
    }

    fn query_shape_summary_record(s: &Summary) -> JsonValue {
        let samples = &s.query_shape_samples;
        if samples.is_empty() {
            return JsonValue::Null;
        }
        let extract_result_bits = sum_shape(samples, |sample| sample.extract_result_bits);
        let extract_source_bits = sum_shape(samples, |sample| sample.extract_source_bits);
        let demand_ratio = if extract_source_bits == 0 {
            JsonValue::Null
        } else {
            #[allow(clippy::cast_precision_loss)]
            JsonValue::from(extract_result_bits as f64 / extract_source_bits as f64)
        };
        json!({
            "profiled_instances": s.query_shape_files,
            "counting_unit": "unique original-query DAG nodes",
            "formula_distributions": {
                "assertions": count_distribution_record(samples, |sample| sample.assertions),
                "dag_nodes": count_distribution_record(samples, |sample| sample.dag_nodes),
                "tree_nodes": count_distribution_record(samples, |sample| sample.tree_nodes),
                "max_depth": count_distribution_record(samples, |sample| sample.max_depth),
                "distinct_symbols": count_distribution_record(
                    samples,
                    |sample| sample.distinct_symbols,
                ),
            },
            "width_distributions": {
                "bitvec_nodes": count_distribution_record(samples, |sample| sample.bitvec_nodes),
                "distinct_bitvec_widths": count_distribution_record(
                    samples,
                    |sample| sample.distinct_bitvec_widths,
                ),
                "max_bitvec_width": count_distribution_record(
                    samples,
                    |sample| sample.max_bitvec_width,
                ),
            },
            "operator_totals": {
                "extract": sum_shape(samples, |sample| sample.extracts),
                "concat": sum_shape(samples, |sample| sample.concats),
                "zero_extend": sum_shape(samples, |sample| sample.zero_exts),
                "sign_extend": sum_shape(samples, |sample| sample.sign_exts),
                "select": sum_shape(samples, |sample| sample.selects),
                "store": sum_shape(samples, |sample| sample.stores),
            },
            "operator_distributions": {
                "extract": count_distribution_record(samples, |sample| sample.extracts),
                "concat": count_distribution_record(samples, |sample| sample.concats),
                "extensions": count_distribution_record(
                    samples,
                    |sample| sample.zero_exts + sample.sign_exts,
                ),
                "array_select_store": count_distribution_record(
                    samples,
                    |sample| sample.selects + sample.stores,
                ),
            },
            "extract_demand": {
                "result_bits": extract_result_bits,
                "source_bits": extract_source_bits,
                "result_over_source_ratio": demand_ratio,
                "narrow_extracts": sum_shape(samples, |sample| sample.narrow_extracts),
            },
            "coercion_cancellation_opportunities": {
                "total": sum_shape(samples, QueryShapeSample::cancellation_opportunities),
                "extract_over_concat": sum_shape(samples, |sample| sample.extract_over_concat),
                "extract_over_extract": sum_shape(samples, |sample| sample.extract_over_extract),
                "extract_over_zero_extend": sum_shape(
                    samples,
                    |sample| sample.extract_over_zero_ext,
                ),
                "extract_over_sign_extend": sum_shape(
                    samples,
                    |sample| sample.extract_over_sign_ext,
                ),
                "exact_low_extract_over_zero_extend": sum_shape(
                    samples,
                    |sample| sample.low_extract_over_zero_ext,
                ),
            },
            "memory_provenance": {
                "surviving_select_store_ops": sum_shape(
                    samples,
                    |sample| sample.selects + sample.stores,
                ),
                "limitation": "memory-derived provenance flattened to BV terms is not inferable; retain it in manifest family/source metadata",
            },
        })
    }

    /// Corpus layer attribution: per-stage seconds, p50/p95 distributions, each
    /// stage's share of the pure-Rust cold pipeline, and the gate (a) verdict on
    /// whether SAT solve time dominates. `null` when no `sat-bv` instance was
    /// decided (the breakdown would be vacuous and a fabricated `0` share could
    /// be misread as "SAT does not dominate").
    fn layer_attribution_record(s: &Summary) -> JsonValue {
        if s.layer_files == 0 {
            return JsonValue::Null;
        }
        let total = s.layer_word_preprocess_s
            + s.layer_bit_blast_s
            + s.layer_cnf_encode_s
            + s.layer_cnf_inprocess_s
            + s.layer_solve_s
            + s.layer_model_lift_s
            + s.layer_model_replay_s;
        let share = |stage: f64| if total > 0.0 { stage / total } else { 0.0 };
        let sat_share = share(s.layer_solve_s);
        json!({
            "instances": s.layer_files,
            "total_pipeline_s": total,
            "word_preprocess_s": s.layer_word_preprocess_s,
            "bit_blast_s": s.layer_bit_blast_s,
            "cnf_encode_s": s.layer_cnf_encode_s,
            "cnf_inprocess_s": s.layer_cnf_inprocess_s,
            "solve_s": s.layer_solve_s,
            "model_lift_s": s.layer_model_lift_s,
            "model_replay_s": s.layer_model_replay_s,
            "model_replay_instances": s.layer_model_replay_files,
            "word_preprocess_share": share(s.layer_word_preprocess_s),
            "bit_blast_share": share(s.layer_bit_blast_s),
            "cnf_encode_share": share(s.layer_cnf_encode_s),
            "cnf_inprocess_share": share(s.layer_cnf_inprocess_s),
            "solve_share": sat_share,
            "model_lift_share": share(s.layer_model_lift_s),
            "model_replay_share": share(s.layer_model_replay_s),
            "distributions": {
                "total": timing_distribution_record(&s.layer_samples, LayerSample::total_s),
                "word_preprocess": timing_distribution_record(
                    &s.layer_samples,
                    |sample| sample.word_preprocess,
                ),
                "bit_blast": timing_distribution_record(
                    &s.layer_samples,
                    |sample| sample.bit_blast,
                ),
                "cnf_encode": timing_distribution_record(
                    &s.layer_samples,
                    |sample| sample.cnf_encode,
                ),
                "cnf_inprocess": timing_distribution_record(
                    &s.layer_samples,
                    |sample| sample.cnf_inprocess,
                ),
                "solve": timing_distribution_record(&s.layer_samples, |sample| sample.solve),
                "model_lift": timing_distribution_record(
                    &s.layer_samples,
                    |sample| sample.model_lift,
                ),
                "model_replay": timing_distribution_record(
                    &s.layer_samples,
                    |sample| sample.model_replay,
                ),
            },
            "size_distributions": {
                "aig_inputs": count_distribution_record(
                    &s.layer_samples,
                    |sample| sample.aig_inputs,
                ),
                "aig_nodes": count_distribution_record(
                    &s.layer_samples,
                    |sample| sample.aig_nodes,
                ),
                "cnf_variables": count_distribution_record(
                    &s.layer_samples,
                    |sample| sample.cnf_variables,
                ),
                "cnf_clauses": count_distribution_record(
                    &s.layer_samples,
                    |sample| sample.cnf_clauses,
                ),
            },
            // Gate (a): does SAT solve time dominate end-to-end? The CDCL-core
            // priority gate needs this and a CaDiCaL/Kissat gap before it jumps
            // the queue ahead of encoding work.
            "sat_dominates": sat_share > SAT_DOMINATES_SHARE,
            "sat_dominates_threshold": SAT_DOMINATES_SHARE,
        })
    }

    /// Fair cold comparison over the original query. Axeyum's side includes its
    /// selected word preprocessing; the in-process Z3 side receives the untouched
    /// assertions and includes its IR translation, solve, and model lift. This is
    /// separate from verdict-only binary fallbacks, whose process startup would
    /// make the ratio incomparable to the embedded-client target.
    fn client_comparison_record(s: &Summary) -> JsonValue {
        if s.client_comparison_files == 0 {
            return JsonValue::Null;
        }
        let ratio = if s.client_z3_s > 0.0 {
            s.client_axeyum_s / s.client_z3_s
        } else {
            f64::INFINITY
        };
        json!({
            "instances": s.client_comparison_files,
            "query_boundary": "original parsed assertions for both solvers",
            "axeyum_total_s": s.client_axeyum_s,
            "z3_total_s": s.client_z3_s,
            "axeyum_over_z3_ratio": if ratio.is_finite() {
                JsonValue::from(ratio)
            } else {
                JsonValue::Null
            },
            "axeyum": timing_distribution_record(
                &s.client_comparison_samples,
                |sample| sample.axeyum_s,
            ),
            "z3": timing_distribution_record(
                &s.client_comparison_samples,
                |sample| sample.z3_s,
            ),
        })
    }

    fn instance_layer_record(record: &SolveRecord, word_preprocess: Duration) -> JsonValue {
        let Some(layers) = BvLayerStats::from_solve_stats(&record.stats) else {
            return JsonValue::Null;
        };
        let sample = LayerSample {
            word_preprocess: word_preprocess.as_secs_f64(),
            bit_blast: layers.bit_blast.as_secs_f64(),
            cnf_encode: layers.cnf_encode.as_secs_f64(),
            cnf_inprocess: layers.cnf_inprocess.as_secs_f64(),
            solve: layers.solve.as_secs_f64(),
            model_lift: layers.model_lift.as_secs_f64(),
            model_replay: record.model_replay.as_secs_f64(),
            aig_inputs: layers.aig_inputs,
            aig_nodes: layers.aig_nodes,
            cnf_variables: layers.cnf_variables,
            cnf_clauses: layers.cnf_clauses,
        };
        json!({
            "word_preprocess_ms": sample.word_preprocess * 1000.0,
            "bit_blast_ms": sample.bit_blast * 1000.0,
            "cnf_encode_ms": sample.cnf_encode * 1000.0,
            "cnf_inprocess_ms": sample.cnf_inprocess * 1000.0,
            "solve_ms": sample.solve * 1000.0,
            "model_lift_ms": sample.model_lift * 1000.0,
            "model_replay_ms": sample.model_replay * 1000.0,
            "total_ms": sample.total_s() * 1000.0,
            "aig_inputs": layers.aig_inputs,
            "aig_nodes": layers.aig_nodes,
            "cnf_variables": layers.cnf_variables,
            "cnf_clauses": layers.cnf_clauses,
        })
    }

    /// Applies the bounded-string `unsat` gate (P2.7 A.2 / ADR-0052) to a solve
    /// record, mirroring the `solve_smtlib` front door: an `unsat` on a script
    /// that used the bounded string/sequence encoding is confirmed
    /// bound-independent or downgraded to `unknown` (an encoding-bound artifact
    /// is never measured as a decision). A confirmation error downgrades too —
    /// conservative, never a fabricated verdict.
    fn gate_bounded_string_record(
        script: &mut Script,
        solved_assertions: &[TermId],
        config: &SolverConfig,
        record: &mut SolveRecord,
    ) {
        if !script.uses_bounded_strings {
            return;
        }
        match record.outcome {
            // Confirm a bounded `unsat` bound-independent, or downgrade it.
            "unsat" => {
                let confirmed = axeyum_solver::confirm_bounded_string_verdict(
                    script,
                    solved_assertions,
                    config,
                    CheckResult::Unsat,
                );
                if !matches!(confirmed, Ok(CheckResult::Unsat)) {
                    record.outcome = "unknown";
                    record.detail = Some(
                        "bounded-string unsat not confirmed bound-independent (P2.7 A.2 \
                         gate); reported unknown"
                            .to_owned(),
                    );
                }
            }
            // Attempt the sound length/code-abstraction upgrade (P2.7 A.2
            // code/len↔LIA): promote to `unsat` only when the abstraction refutes
            // (e.g. a `str.to_code` range/arithmetic conflict the bounded integer
            // bit-blast could not close — `str-code-unsat*`).
            "unknown" => {
                if let Ok(CheckResult::Unsat) =
                    axeyum_solver::upgrade_bounded_string_unknown(script, solved_assertions, config)
                {
                    record.outcome = "unsat";
                    record.detail = Some(
                        "bounded-string unknown upgraded to unsat by the unbounded \
                         length/code abstraction (P2.7 A.2 code/len↔LIA)"
                            .to_owned(),
                    );
                }
            }
            _ => {}
        }
    }

    /// Normal-path word-route upgrade (T-B.7 slice 2) — harness parity with the
    /// `solve_smtlib` front door's second-chance word route. After the bounded
    /// gate leaves a string script `unknown` (the bounded path declined or the
    /// ADR-0052 gate downgraded a bound-dependent verdict), consult the word route:
    /// it may decide `unsat` through the independently re-checked derivation
    /// (ADR-0053 T-B.7) or `sat` through the in-crate `Seq`-level replay. Runs
    /// **before** the oracle comparison so the upgraded verdict flows into it.
    ///
    /// A word-route `sat` model is a `Seq`-level witness already checked in-crate;
    /// it is NOT replayed against the packed bit-vector view, so `model_replay_failure`
    /// is kept `false` (a packed replay would spuriously fail on the empty/gated view).
    fn apply_word_route_upgrade(
        script: &mut Script,
        config: &SolverConfig,
        record: &mut SolveRecord,
    ) {
        if record.outcome != "unknown" || script.word_problem.is_none() {
            return;
        }
        match axeyum_solver::word_route_verdict(script, config) {
            Some(CheckResult::Sat(_)) => {
                record.outcome = "sat";
                record.detail = Some(
                    "word-equation route (T-B.7): decided sat; model replayed \
                     in-crate at the Seq level"
                        .to_owned(),
                );
                record.model_replay_failure = false;
            }
            Some(CheckResult::Unsat) => {
                record.outcome = "unsat";
                record.detail = Some(
                    "word-equation route (T-B.7): decided unsat via an independently \
                     re-checked derivation"
                        .to_owned(),
                );
                record.model_replay_failure = false;
            }
            _ => {}
        }
    }

    /// Online CDCL(T) string second chance (P1.5b) — harness parity with the
    /// `solve_smtlib` front door's `apply_online_string_route`, run **strictly after**
    /// [`apply_word_route_upgrade`] leaves the record `unknown`. It decides the
    /// Boolean-structured word problems (`or`/negated shapes) the flat conjunction
    /// route cannot represent, over the parser's [`Script::word_skeleton`] `Seq`-level
    /// view — a certified theory `unsat` or a replay-checked `sat`.
    ///
    /// A `sat` model is a `Seq`-level witness already replayed against the original
    /// assertions inside the entry point; it is NOT replayed against the packed
    /// bit-vector view, so `model_replay_failure` stays `false` (a packed replay would
    /// spuriously fail on the empty/gated view). Runs **before** the oracle comparison
    /// so the upgraded verdict is what the z3-binary cross-check sees.
    fn apply_online_string_upgrade(
        script: &mut Script,
        config: &SolverConfig,
        record: &mut SolveRecord,
    ) {
        if record.outcome != "unknown" || script.word_skeleton.is_empty() {
            return;
        }
        match axeyum_solver::online_string_verdict(script, config) {
            Some(CheckResult::Sat(_)) => {
                record.outcome = "sat";
                record.detail = Some(
                    "online CDCL(T) string route (P1.5b): decided sat; model replayed \
                     in-crate at the Seq level"
                        .to_owned(),
                );
                record.model_replay_failure = false;
            }
            Some(CheckResult::Unsat) => {
                record.outcome = "unsat";
                record.detail = Some(
                    "online CDCL(T) string route (P1.5b): decided unsat via a certified \
                     theory conflict"
                        .to_owned(),
                );
                record.model_replay_failure = false;
            }
            _ => {}
        }
    }

    /// Regex-membership second chance (P2.7 T-C.5) — harness parity with the
    /// `solve_smtlib` front door's `apply_membership_route`, run **strictly after**
    /// [`apply_online_string_upgrade`] leaves the record `unknown`. It decides the
    /// `str.in_re` membership problems the parser captured in
    /// [`Script::membership_problem`] over the symbolic-derivative sub-solver — a
    /// matcher-replayed `sat` witness or a re-checked-emptiness `unsat`.
    ///
    /// A `sat` model is a `Seq`-level witness already replayed through the reference
    /// matcher against every membership atom; it is NOT replayed against the packed
    /// bit-vector view, so `model_replay_failure` stays `false`. Runs **before** the
    /// oracle comparison so the upgraded verdict is what the z3-binary cross-check
    /// sees.
    fn apply_membership_upgrade(
        script: &mut Script,
        config: &SolverConfig,
        record: &mut SolveRecord,
    ) {
        if record.outcome != "unknown" || script.membership_problem.is_none() {
            return;
        }
        match axeyum_solver::membership_verdict(script, config) {
            Some(CheckResult::Sat(_)) => {
                record.outcome = "sat";
                record.detail = Some(
                    "regex-membership route (T-C.5): decided sat; witness replayed \
                     in-crate through the reference matcher"
                        .to_owned(),
                );
                record.model_replay_failure = false;
            }
            Some(CheckResult::Unsat) => {
                record.outcome = "unsat";
                record.detail = Some(
                    "regex-membership route (T-C.5): decided unsat via a re-checked \
                     derivative-emptiness certificate"
                        .to_owned(),
                );
                record.model_replay_failure = false;
            }
            _ => {}
        }
    }

    /// Applies the **lexicographic-order route** upgrade (P2.7 T-C.6) — harness
    /// parity with the `solve_smtlib` front door's `apply_lex_order_route`, run
    /// **strictly after** [`apply_membership_upgrade`] leaves the record `unknown`.
    /// It decides the `str.<=` / `str.<` problems the parser captured in
    /// [`Script::lex_problem`] via the certified refuter — a variable-independent
    /// constant fold or a transitivity + first-character clash. It only ever adds a
    /// re-checked `unsat` (never `sat`). Runs **before** the oracle comparison so the
    /// upgraded verdict is what the z3-binary cross-check sees.
    fn apply_lex_order_upgrade(
        script: &mut Script,
        config: &SolverConfig,
        record: &mut SolveRecord,
    ) {
        if record.outcome != "unknown" || script.lex_problem.is_none() {
            return;
        }
        if let Some(CheckResult::Unsat) = axeyum_solver::lex_order_verdict(script, config) {
            record.outcome = "unsat";
            record.detail = Some(
                "lexicographic-order route (T-C.6): decided unsat via a re-checked \
                 constant fold or transitivity + first-character clash"
                    .to_owned(),
            );
            record.model_replay_failure = false;
        }
    }

    /// Decides a **word-first-fallback** script (T-B.4d) — harness parity with
    /// the `solve_smtlib` front door. The flat assertion view is empty (the
    /// bounded ADR-0029 encoder declined at parse), so the sat-only,
    /// replay-checked word-equation route is the sole decider. On `sat` the
    /// model has already replayed against every equality/disequality through
    /// the ground evaluator inside `axeyum-strings` (the trust anchor); the
    /// oracle cross-check is verdict-only via the **Z3 binary** on the original
    /// file (the in-repo library oracle would compare the vacuous empty view).
    /// On a word-route decline the instance keeps the exact `unsupported`
    /// classification (and original bounded parse error) it had before the
    /// fallback existed — never a silently reshaped bucket.
    fn run_word_only(
        file: &Path,
        name: &str,
        script: &mut Script,
        timeout: Duration,
        args: &Args,
        summary: &mut Summary,
    ) -> JsonValue {
        let config = solver_config(args, timeout);
        let start = Instant::now();
        let decided = axeyum_solver::decide_word_only_script(script, &config);
        let solve = start.elapsed();
        // The word route (T-B.4d) and the online CDCL(T) skeleton route (P1.5b) may
        // both decide a word-first-fallback script: `sat` (a `Seq`-level replay-checked
        // model) or `unsat` (a certified derivation / theory conflict). Both are real
        // verdicts; a `sat` model is NOT replayed against the empty packed view.
        let verdict = match &decided {
            Ok(CheckResult::Sat(_)) => Some("sat"),
            Ok(CheckResult::Unsat) => Some("unsat"),
            _ => None,
        };
        if let Some(verdict) = verdict {
            if verdict == "sat" {
                summary.sat += 1;
            } else {
                summary.unsat += 1;
            }
            summary.par2_seconds += solve.as_secs_f64();
            let oracle = if args.compare_z3 {
                if let Some(result) = run_z3_binary(file, config.timeout) {
                    let compared = result.verdict.is_some();
                    let agrees = result.verdict == Some(verdict);
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
                    json!({
                        "enabled": true,
                        "backend_kind": "z3-binary",
                        "outcome": result.verdict,
                        "decision_compared": compared,
                        "decision_agrees": if compared {
                            JsonValue::Bool(agrees)
                        } else {
                            JsonValue::Null
                        },
                        "z3_binary": {
                            "verdict": result.verdict,
                            "raw": result.raw,
                            "solve_ms": result.elapsed_ms,
                        },
                    })
                } else {
                    summary.oracle_skipped += 1;
                    json!({ "enabled": true, "skipped": "z3-binary-unavailable" })
                }
            } else {
                JsonValue::Null
            };
            return json!({
                "file": name,
                "outcome": verdict,
                "detail": "word-first fallback (T-B.4d) / online CDCL(T) string route \
                           (P1.5b): decided by the word-level string routes (sat models \
                           replay in-crate at the Seq level; unsat is a certified \
                           derivation)",
                "word_only": true,
                "solve_ms": duration_ms(solve),
                "oracle": oracle,
            });
        }
        // Decline: the front door reproduces the original bounded parse
        // error; the harness keeps the pre-fallback `unsupported` bucket.
        summary.unsupported += 1;
        json!({
            "file": name,
            "outcome": "unsupported",
            "detail": script.word_only_fallback.clone().unwrap_or_default(),
            "word_only": true,
            "word_route_declined": true,
            "solve_ms": duration_ms(solve),
        })
    }

    /// Runs one instance and returns its JSON record.
    #[allow(clippy::too_many_lines)]
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
        // T-B.4d harness parity with the `solve_smtlib` front door: a word-only
        // fallback script has an EMPTY flat assertion view (the bounded encoder
        // declined at parse) — handing it to the backend would answer a vacuous
        // `sat`. The word route is its only decider; a decline restores the exact
        // pre-fallback `unsupported` classification.
        if script.word_only_fallback.is_some()
            && (script.word_problem.is_some() || !script.word_skeleton.is_empty())
        {
            return run_word_only(file, &name, &mut script, timeout, args, summary);
        }
        let input_shape = TermStats::compute(&script.arena, &script.assertions);
        let query_shape =
            QueryShapeSample::compute(&script.arena, &script.assertions, &input_shape);
        summary.query_shape_files += 1;
        summary.query_shape_sample = Some(query_shape);
        let mut rewrite = apply_rewrite(&mut script, args.rewrite);
        // Word-level preprocessing (P1.2): shrink the post-rewrite assertions and
        // keep a reconstruction trail so the sat model still replays against the
        // original query. The reduced set replaces what the backend solves.
        let preprocess_start = Instant::now();
        let preprocess_trail = if args.preprocess {
            let (reduced, trail) = apply_preprocess(&mut script.arena, &rewrite.assertions);
            rewrite.assertions = reduced;
            Some(trail)
        } else {
            None
        };
        let word_preprocess = if args.preprocess {
            preprocess_start.elapsed()
        } else {
            Duration::ZERO
        };
        let output_shape = TermStats::compute(&script.arena, &rewrite.assertions);
        accumulate_rewrite(summary, args.rewrite, &rewrite, &input_shape, &output_shape);
        let config = solver_config(args, timeout);
        let plan_config = PlanSolveConfig::from_args(args);
        let original_solve = if args.rewrite == RewriteMode::Default {
            let mut original = solve_planned(
                backend,
                &script.arena,
                &script.assertions,
                &script.assertions,
                &config,
                plan_config,
                None,
            );
            // Same bounded-string gate as the primary solve below, so the
            // rewrite-decision comparison never flags a gate downgrade as a
            // rewrite-induced verdict change.
            let original_assertions = script.assertions.clone();
            gate_bounded_string_record(&mut script, &original_assertions, &config, {
                &mut original.solve
            });
            // Same word-route second chance as the primary solve, so the
            // rewrite-decision comparison never flags a word-route upgrade as a
            // rewrite-induced verdict change.
            apply_word_route_upgrade(&mut script, &config, &mut original.solve);
            apply_online_string_upgrade(&mut script, &config, &mut original.solve);
            apply_membership_upgrade(&mut script, &config, &mut original.solve);
            apply_lex_order_upgrade(&mut script, &config, &mut original.solve);
            Some(original)
        } else {
            None
        };
        let mut primary_solve = solve_planned(
            backend,
            &script.arena,
            &rewrite.assertions,
            &script.assertions,
            &config,
            plan_config,
            preprocess_trail.as_ref(),
        );
        // Bounded-string gate (P2.7 A.2 / ADR-0052): harness parity with the
        // `solve_smtlib` front door — a bounded-string `unsat` is only measured
        // as `unsat` when confirmed bound-independent; otherwise it is an
        // encoding-bound artifact (the real string theory may be `sat`) and is
        // recorded `unknown`. Without this, the harness would credit — and the
        // z3-binary oracle would flag — verdicts the shipped front door never
        // returns.
        let gated_assertions = rewrite.assertions.clone();
        gate_bounded_string_record(&mut script, &gated_assertions, &config, {
            &mut primary_solve.solve
        });
        // Word-route second chance (T-B.7 slice 2): if the gate (or the bounded
        // path) left this string script `unknown`, let the independently
        // re-checked word route decide it — the same second chance the front door
        // grants. Runs BEFORE the oracle comparison so the upgraded verdict is what
        // `compare_with_oracle` cross-checks.
        apply_word_route_upgrade(&mut script, &config, &mut primary_solve.solve);
        // Online CDCL(T) string second chance (P1.5b): decides the disjunctive word
        // problems the flat route above cannot, before the oracle comparison.
        apply_online_string_upgrade(&mut script, &config, &mut primary_solve.solve);
        // Regex-membership second chance (P2.7 T-C.5): decides the `str.in_re`
        // membership problems by symbolic derivatives, before the oracle comparison.
        apply_membership_upgrade(&mut script, &config, &mut primary_solve.solve);
        // Lexicographic-order second chance (P2.7 T-C.6): decides the `str.<=`/`str.<`
        // problems by the certified refuter, before the oracle comparison.
        apply_lex_order_upgrade(&mut script, &config, &mut primary_solve.solve);
        if let Some(original) = &original_solve {
            compare_rewrite_decision(&original.solve, &primary_solve.solve, summary);
        }
        let oracle_record = compare_backend.as_deref_mut().map(|backend| {
            compare_with_oracle(
                backend,
                file,
                &script,
                &primary_solve.solve,
                &config,
                summary,
                word_preprocess,
            )
        });
        accumulate_query_plan(summary, &primary_solve.plan);
        accumulate_primary(&primary_solve.solve, summary);
        accumulate_proof_replay(&primary_solve.solve, args.prove_unsat, summary);
        accumulate_par2(summary, &primary_solve.solve, word_preprocess, timeout);
        accumulate_layers(summary, &primary_solve.solve, word_preprocess);
        accumulate_expected_agreement(summary, script.status.as_deref(), &primary_solve.solve);
        let stats = &primary_solve.solve.stats;
        let mut record = json!({
            "file": name,
            "outcome": primary_solve.solve.outcome,
            "expected": script.status.as_deref().unwrap_or("unknown"),
            "cold_total_ms": duration_ms_f64(
                word_preprocess
                    + stats.translate
                    + stats.solve
                    + stats.model_lift
                    + primary_solve.solve.model_replay
            ),
            "translate_ms": duration_ms(stats.translate),
            "solve_ms": duration_ms(stats.solve),
            "model_lift_ms": duration_ms(stats.model_lift),
            "model_replay_ms": duration_ms_f64(primary_solve.solve.model_replay),
            "unsat_proof_replay": proof_replay_status(&primary_solve.solve, args.prove_unsat),
            "unsat_proof_replay_ms": proof_replay_duration(&primary_solve.solve)
                .map(duration_ms_f64),
            "backend_stats": backend_stats_record(stats),
            "layer_attribution": instance_layer_record(&primary_solve.solve, word_preprocess),
            "dag_nodes": input_shape.dag_nodes,
            "tree_nodes": input_shape.tree_nodes,
            "max_depth": input_shape.max_depth,
            "distinct_symbols": input_shape.distinct_symbols,
            "assertions": usize_to_u64(script.assertions.len()),
            "query_shape": query_shape_record(query_shape),
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
            resource_limit: args.resource_limit,
            node_budget: args.node_budget,
            cnf_variable_budget: args.cnf_variable_budget,
            cnf_clause_budget: args.cnf_clause_budget,
            cnf_inprocessing: args.cnf_inprocessing,
            cnf_vivify: args.cnf_vivify,
            native_cdcl: args.native_cdcl,
            prove_unsat: args.prove_unsat,
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
            Ok(s) => {
                // Soundness guard: never report a real verdict for a benchmark the
                // slice-parser could not faithfully represent. The harness solves the
                // *flat* `assertions` view; if the script's actual decision query
                // includes inline assumptions, or the file plainly carries constraints
                // the flat view dropped, solving the flat view would answer a
                // *different* (often vacuously satisfiable) problem and could
                // false-alarm against `:status` — see [`under_parsed_reason`].
                if let Some(reason) = under_parsed_reason(&s, &text) {
                    summary.unsupported += 1;
                    return Err(json!({
                        "file": name,
                        "outcome": "unsupported",
                        "detail": reason,
                    }));
                }
                Ok(s)
            }
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

    /// Detects a benchmark the slice-parser under-represented, so the harness can
    /// mark it `unsupported` instead of reporting a (possibly vacuous) verdict that
    /// would silently solve a *different* problem than the source asked — and could
    /// false-alarm against `:status` or, worse, hide a real disagreement. Returns
    /// `Some(reason)` when under-parsed, `None` when the flat assertion view is a
    /// faithful encoding of the script's decision query.
    ///
    /// Two cases are detected (the minimum the course-correction calls out):
    ///
    /// 1. **`check-sat-assuming` with inline assumptions.** The flat `assertions`
    ///    view omits the per-`check-sat` assumption literals, so solving it answers a
    ///    strictly weaker query. (An *empty* assumption list is equivalent to
    ///    `check-sat`, so it is not flagged.)
    /// 2. **Zero assertions parsed from a non-trivial file.** The flat view is empty,
    ///    yet the raw source contains an `assert`/`constraint`/`check-sat-assuming`
    ///    token — i.e. constraints the slice could not represent were dropped, and
    ///    solving "no constraints" is a vacuous `sat`.
    fn under_parsed_reason(script: &Script, text: &str) -> Option<String> {
        // T-B.4d word-first fallback: the flat view is empty because the bounded
        // encoder declined at parse, but a word-problem side channel carries the
        // constraints FAITHFULLY — either the flat top-level-conjunction
        // `word_problem`, or (the disjunctive `str002` census shape, P1.5b) the
        // Boolean-structured `word_skeleton`. `run_one` decides such a script via the
        // word / online CDCL(T) string routes (never the vacuous flat view) under the
        // SAME condition, so it is not under-parsed. Mirrors the dispatch guard in
        // `run_one`.
        if script.word_only_fallback.is_some()
            && (script.word_problem.is_some() || !script.word_skeleton.is_empty())
        {
            return None;
        }
        if script.commands.iter().any(|cmd| {
            matches!(cmd, ScriptCommand::CheckSatAssuming(assumptions) if !assumptions.is_empty())
        }) {
            return Some(
                "check-sat-assuming with inline assumptions not represented by the flat \
                 assertion view; solving it would answer a weaker query"
                    .to_owned(),
            );
        }
        if script.assertions.is_empty() && source_has_constraints(text) {
            return Some(
                "0 assertions parsed from a file containing assert/constraint text; the \
                 slice-parser dropped constraints — solving the empty problem would be a \
                 vacuous verdict"
                    .to_owned(),
            );
        }
        None
    }

    /// Whether the raw SMT-LIB source carries any constraint-bearing token. A coarse
    /// substring scan is deliberate: the goal is only to distinguish a genuinely
    /// empty benchmark (no constraints, where an empty assertion view is faithful)
    /// from one whose constraints the parser silently dropped.
    fn source_has_constraints(text: &str) -> bool {
        text.contains("(assert")
            || text.contains("(constraint")
            || text.contains("check-sat-assuming")
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
        // Deterministic node-fuel bail (see `axeyum_rewrite::solve_eqs_bounded`): the
        // substitution loop runs effectively unbounded on the large public ite-DAGs,
        // so cap it to a sound partial reduction instead of hanging the harness.
        let (reduced, eq_trail) = solve_eqs_bounded(arena, &after_values, DEFAULT_SOLVE_EQS_FUEL)
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
        model_replay: Duration,
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
        total_model_replay: Duration,
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
                total_model_replay: Duration::ZERO,
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
                    let replay_start = Instant::now();
                    let mut finished = self.handle_sat_model(problem, plan, &model, round);
                    self.total_model_replay += replay_start.elapsed();
                    if let Some(result) = &mut finished {
                        result.solve.model_replay = self.total_model_replay;
                    }
                    finished
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
                self.total_model_replay,
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
        let (outcome, detail, model_replay_failure, model_replay) = classify_result(
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
            model_replay,
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
        model_replay: Duration,
        plan: QueryPlan,
        refinement: RefinementRecord,
    ) -> PlannedSolve {
        PlannedSolve {
            solve: SolveRecord {
                outcome,
                detail,
                stats,
                model_replay,
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
    ) -> (&'static str, Option<String>, bool, Duration) {
        match result {
            Ok(CheckResult::Sat(model)) => {
                let replay_start = Instant::now();
                match replay_model(arena, replay_assertions, &model, reconstruct) {
                    Ok(()) => ("sat", None, false, replay_start.elapsed()),
                    Err(e) if replay_failure_policy == ReplayFailurePolicy::DowngradeToUnknown => (
                        "unknown",
                        Some(format!(
                            "Incomplete: sliced sat model did not replay original query: {e}"
                        )),
                        false,
                        replay_start.elapsed(),
                    ),
                    Err(e) => ("model-replay-error", Some(e), true, replay_start.elapsed()),
                }
            }
            Ok(CheckResult::Unsat) => ("unsat", None, false, Duration::ZERO),
            Ok(CheckResult::Unknown(r)) => (
                "unknown",
                Some(format!("{:?}: {}", r.kind, r.detail)),
                false,
                Duration::ZERO,
            ),
            Err(SolverError::Unsupported(detail)) => {
                ("unsupported", Some(detail), false, Duration::ZERO)
            }
            Err(e) => ("solver-error", Some(e.to_string()), false, Duration::ZERO),
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
        // Root-cause bucket for every non-decided instance. For `unknown`, the
        // precise `UnknownKind` is the prefix of the detail string (recorded as
        // `"{:?}: {}"`, e.g. `"Timeout: ..."`); fall back to the bare outcome.
        if !matches!(record.outcome, "sat" | "unsat") {
            let key = if record.outcome == "unknown" {
                let kind = record
                    .detail
                    .as_deref()
                    .and_then(|d| d.split(':').next())
                    .map(str::trim)
                    .filter(|k| !k.is_empty())
                    .unwrap_or("Unclassified");
                format!("unknown:{kind}")
            } else {
                record.outcome.to_owned()
            };
            *summary.blocker_buckets.entry(key).or_insert(0) += 1;
        }
    }

    fn proof_replay_status(record: &SolveRecord, requested: bool) -> &'static str {
        if record.outcome != "unsat" {
            return "not-applicable";
        }
        if !requested {
            return "not-requested";
        }
        let checked = record.stats.backend.iter().any(|(name, value)| {
            matches!(
                name.as_str(),
                "unsat_proof_checked" | "unsat_proof_checked_inline"
            ) && *value > 0.0
        });
        if checked && proof_replay_duration(record).is_some() {
            "checked"
        } else {
            "missing"
        }
    }

    fn proof_replay_duration(record: &SolveRecord) -> Option<Duration> {
        record
            .stats
            .backend
            .iter()
            .find(|(name, _)| name == "unsat_proof_replay_ms")
            .and_then(|(_, milliseconds)| {
                let seconds = milliseconds / 1000.0;
                (seconds.is_finite() && seconds >= 0.0).then(|| Duration::from_secs_f64(seconds))
            })
    }

    fn accumulate_proof_replay(record: &SolveRecord, requested: bool, summary: &mut Summary) {
        match proof_replay_status(record, requested) {
            "checked" => {
                let duration = proof_replay_duration(record)
                    .expect("checked proof replay status carries a duration");
                summary.unsat_proof_replay_checked += 1;
                summary.unsat_proof_replay_s += duration.as_secs_f64();
                summary.unsat_proof_replay_sample = Some(duration.as_secs_f64());
            }
            "missing" => summary.unsat_proof_replay_missing += 1,
            "not-applicable" | "not-requested" => {}
            _ => unreachable!("proof replay status is closed"),
        }
    }

    /// Formats the blocker buckets most-frequent-first (ties broken by key) into a
    /// compact `key=count …` leaderboard line.
    fn blocker_leaderboard(buckets: &BTreeMap<String, u64>) -> String {
        let mut ranked: Vec<(&String, &u64)> = buckets.iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
        ranked
            .iter()
            .map(|(k, n)| format!("{k}={n}"))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// Rolls a decided pure-Rust instance into the corpus layer attribution.
    ///
    /// Only `sat`/`unsat` instances solved by the `sat-bv` backend contribute:
    /// [`BvLayerStats::from_solve_stats`] returns `None` for any other backend,
    /// so this never fabricates a stage breakdown for, e.g., the Z3 oracle. The
    /// `translate` stage comes straight from [`SolveStats`].
    fn accumulate_layers(summary: &mut Summary, record: &SolveRecord, word_preprocess: Duration) {
        if !matches!(record.outcome, "sat" | "unsat") {
            return;
        }
        let Some(layers) = BvLayerStats::from_solve_stats(&record.stats) else {
            return;
        };
        let sample = LayerSample {
            word_preprocess: word_preprocess.as_secs_f64(),
            bit_blast: layers.bit_blast.as_secs_f64(),
            cnf_encode: layers.cnf_encode.as_secs_f64(),
            cnf_inprocess: layers.cnf_inprocess.as_secs_f64(),
            solve: layers.solve.as_secs_f64(),
            model_lift: layers.model_lift.as_secs_f64(),
            model_replay: record.model_replay.as_secs_f64(),
            aig_inputs: layers.aig_inputs,
            aig_nodes: layers.aig_nodes,
            cnf_variables: layers.cnf_variables,
            cnf_clauses: layers.cnf_clauses,
        };
        summary.layer_files += 1;
        summary.layer_word_preprocess_s += sample.word_preprocess;
        summary.layer_bit_blast_s += layers.bit_blast.as_secs_f64();
        summary.layer_cnf_encode_s += layers.cnf_encode.as_secs_f64();
        summary.layer_cnf_inprocess_s += layers.cnf_inprocess.as_secs_f64();
        summary.layer_solve_s += layers.solve.as_secs_f64();
        summary.layer_model_lift_s += layers.model_lift.as_secs_f64();
        summary.layer_model_replay_s += record.model_replay.as_secs_f64();
        summary.layer_model_replay_files += u64::from(record.outcome == "sat");
        summary.layer_sample = Some(sample);
    }

    fn accumulate_par2(
        summary: &mut Summary,
        record: &SolveRecord,
        word_preprocess: Duration,
        timeout: Duration,
    ) {
        if matches!(record.outcome, "sat" | "unsat") {
            summary.par2_seconds += word_preprocess.as_secs_f64()
                + record.stats.translate.as_secs_f64()
                + record.stats.solve.as_secs_f64()
                + record.stats.model_lift.as_secs_f64()
                + record.model_replay.as_secs_f64();
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

    fn annotate_manifest_result(
        record: &mut JsonValue,
        entry: &CorpusManifestEntry,
        summary: &mut Summary,
    ) {
        summary.manifest_expected += 1;
        let outcome = record
            .get("outcome")
            .and_then(JsonValue::as_str)
            .map(str::to_owned);
        let agrees = match outcome.as_deref() {
            Some("sat" | "unsat") => {
                summary.manifest_compared += 1;
                if outcome.as_deref() == Some(entry.expected.as_str()) {
                    summary.manifest_agree += 1;
                    true
                } else {
                    summary.manifest_disagree += 1;
                    false
                }
            }
            _ => false,
        };
        if let JsonValue::Object(object) = record {
            object.insert(
                "corpus_manifest".to_owned(),
                json!({
                    "path": entry.path,
                    "content_hash": entry.content_hash,
                    "expected": entry.expected,
                    "family": entry.family,
                    "tiers": entry.tiers,
                    "decision_compared": matches!(outcome.as_deref(), Some("sat" | "unsat")),
                    "decision_agrees": if matches!(outcome.as_deref(), Some("sat" | "unsat")) {
                        JsonValue::Bool(agrees)
                    } else {
                        JsonValue::Null
                    },
                }),
            );
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
        total.unsat_proof_replay_checked += next.unsat_proof_replay_checked;
        total.unsat_proof_replay_missing += next.unsat_proof_replay_missing;
        total.unsat_proof_replay_s += next.unsat_proof_replay_s;
        if let Some(sample) = next.unsat_proof_replay_sample {
            total.unsat_proof_replay_samples.push(sample);
        }
        for (key, count) in &next.blocker_buckets {
            *total.blocker_buckets.entry(key.clone()).or_insert(0) += count;
        }
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
        // Tree-node counts are the DAG-to-tree expansion metric — a single
        // heavily-shared script (e.g. a deeply-nested regex membership) can
        // exponentially exceed `u64`. These are diagnostics, not soundness, so
        // saturate rather than panic the whole run.
        total.query_original_tree_nodes = total
            .query_original_tree_nodes
            .saturating_add(next.query_original_tree_nodes);
        total.query_slice_tree_nodes = total
            .query_slice_tree_nodes
            .saturating_add(next.query_slice_tree_nodes);
        total.oracle_compared += next.oracle_compared;
        total.oracle_agree += next.oracle_agree;
        total.oracle_disagree += next.oracle_disagree;
        total.oracle_skipped += next.oracle_skipped;
        total.par2_seconds += next.par2_seconds;
        total.layer_files += next.layer_files;
        total.layer_word_preprocess_s += next.layer_word_preprocess_s;
        total.layer_bit_blast_s += next.layer_bit_blast_s;
        total.layer_cnf_encode_s += next.layer_cnf_encode_s;
        total.layer_cnf_inprocess_s += next.layer_cnf_inprocess_s;
        total.layer_solve_s += next.layer_solve_s;
        total.layer_model_lift_s += next.layer_model_lift_s;
        total.layer_model_replay_s += next.layer_model_replay_s;
        total.layer_model_replay_files += next.layer_model_replay_files;
        if let Some(sample) = next.layer_sample {
            total.layer_samples.push(sample);
        }
        total.query_shape_files += next.query_shape_files;
        if let Some(sample) = next.query_shape_sample {
            total.query_shape_samples.push(sample);
        }
        total.client_comparison_files += next.client_comparison_files;
        total.client_axeyum_s += next.client_axeyum_s;
        total.client_z3_s += next.client_z3_s;
        if let Some(sample) = next.client_comparison_sample {
            total.client_comparison_samples.push(sample);
        }
        total.manifest_expected += next.manifest_expected;
        total.manifest_compared += next.manifest_compared;
        total.manifest_agree += next.manifest_agree;
        total.manifest_disagree += next.manifest_disagree;
    }

    #[allow(clippy::too_many_arguments)]
    fn compare_with_oracle(
        oracle: &mut dyn SolverBackend,
        file: &Path,
        script: &Script,
        primary: &SolveRecord,
        config: &SolverConfig,
        summary: &mut Summary,
        word_preprocess: Duration,
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
            &script.assertions,
            &script.assertions,
            &oracle_config,
            ReplayFailurePolicy::SoundnessAlarm,
            None,
        );
        let mut compared = matches!(oracle_solve.outcome, "sat" | "unsat");
        // The in-repo `Z3Backend` oracle only supports `QF_BV` (it returns
        // `unsupported` for UF/arithmetic/datatypes/quantifiers/FP). So for the
        // non-BV divisions this keystone exists to measure, it cannot give a
        // head-to-head. When it declines, fall back to the **Z3 binary** run on the
        // original file — the same verdict a Z3 user would get — so the oracle
        // agree/disagree counters carry a true comparison. This is a verdict-only
        // cross-check (no model lift), which is exactly what a soundness `:status`
        // / disagreement gate needs.
        let mut z3_binary: Option<Z3BinaryResult> = None;
        let mut oracle_outcome = oracle_solve.outcome;
        if !compared && let Some(result) = run_z3_binary(file, config.timeout) {
            if let Some(verdict) = result.verdict {
                oracle_outcome = verdict;
                compared = true;
            }
            z3_binary = Some(result);
        }

        let agrees = compared && oracle_outcome == primary.outcome;
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

        // The client target is embedded libz3, not a subprocess. Record a timing
        // comparison only when the in-repo Z3 backend decided the untouched
        // query; a binary fallback remains a verdict cross-check but its process
        // startup would corrupt the performance ratio.
        if compared && z3_binary.is_none() {
            let sample = ClientComparisonSample {
                axeyum_s: word_preprocess.as_secs_f64()
                    + primary.stats.translate.as_secs_f64()
                    + primary.stats.solve.as_secs_f64()
                    + primary.stats.model_lift.as_secs_f64()
                    + primary.model_replay.as_secs_f64(),
                z3_s: oracle_solve.stats.translate.as_secs_f64()
                    + oracle_solve.stats.solve.as_secs_f64()
                    + oracle_solve.stats.model_lift.as_secs_f64()
                    + oracle_solve.model_replay.as_secs_f64(),
            };
            summary.client_comparison_files += 1;
            summary.client_axeyum_s += sample.axeyum_s;
            summary.client_z3_s += sample.z3_s;
            summary.client_comparison_sample = Some(sample);
        }

        let mut record = json!({
            "enabled": true,
            "backend_kind": if z3_binary.is_some() { "z3-binary" } else { "z3" },
            "query_boundary": "original parsed assertions",
            "outcome": oracle_outcome,
            "decision_compared": compared,
            "decision_agrees": if compared { JsonValue::Bool(agrees) } else { JsonValue::Null },
            "translate_ms": duration_ms(oracle_solve.stats.translate),
            "solve_ms": duration_ms(oracle_solve.stats.solve),
            "model_lift_ms": duration_ms(oracle_solve.stats.model_lift),
            "model_replay_ms": duration_ms_f64(oracle_solve.model_replay),
            "cold_total_ms": duration_ms_f64(
                oracle_solve.stats.translate
                    + oracle_solve.stats.solve
                    + oracle_solve.stats.model_lift
                    + oracle_solve.model_replay
            ),
            "backend_stats": backend_stats_record(&oracle_solve.stats),
        });
        if let JsonValue::Object(obj) = &mut record {
            if let Some(detail) = &oracle_solve.detail {
                obj.insert("in_repo_z3_detail".to_owned(), json!(detail));
            }
            if let Some(result) = &z3_binary {
                obj.insert(
                    "z3_binary".to_owned(),
                    json!({
                        "verdict": result.verdict,
                        "raw": result.raw,
                        "solve_ms": result.elapsed_ms,
                    }),
                );
            }
        }
        record
    }

    /// The verdict a stand-alone Z3 binary returns for one benchmark file.
    struct Z3BinaryResult {
        /// `"sat"` / `"unsat"` when Z3 decided; `None` for `unknown`/timeout/other.
        verdict: Option<&'static str>,
        /// The first non-empty line of Z3's stdout (for the artifact record).
        raw: String,
        elapsed_ms: u64,
    }

    /// Runs the stand-alone Z3 binary on `file` with a per-call timeout, returning
    /// its `(check-sat)` verdict. The binary path is overridable via the `AXEYUM_Z3`
    /// environment variable (default `z3`, resolved on `PATH`). Returns `None` only
    /// when Z3 could not be launched at all (so the caller leaves the instance
    /// `skipped` rather than fabricating a comparison); a Z3 `unknown`/timeout is a
    /// `Some` with `verdict: None`.
    fn run_z3_binary(file: &Path, timeout: Option<Duration>) -> Option<Z3BinaryResult> {
        let binary = std::env::var("AXEYUM_Z3").unwrap_or_else(|_| "z3".to_owned());
        let mut cmd = std::process::Command::new(binary);
        cmd.arg(file);
        if let Some(t) = timeout {
            // Z3's own soft timeout, in milliseconds; keeps a wedged instance from
            // hanging the harness. Add a small margin so Z3's internal timeout fires
            // before any external watchdog.
            cmd.arg(format!("-T:{}", t.as_secs().max(1) + 1));
        }
        let start = Instant::now();
        let output = cmd.output().ok()?;
        let elapsed_ms = duration_ms(start.elapsed());
        let stdout = String::from_utf8_lossy(&output.stdout);
        let first = stdout
            .lines()
            .map(str::trim)
            .find(|line| !line.is_empty())
            .unwrap_or("")
            .to_owned();
        let verdict = match first.as_str() {
            "sat" => Some("sat"),
            "unsat" => Some("unsat"),
            _ => None,
        };
        Some(Z3BinaryResult {
            verdict,
            raw: first,
            elapsed_ms,
        })
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
        match check_model_with_assignment(arena, assertions, model, &assignment) {
            Ok(true) => Ok(()),
            Ok(false) => Err("model or quantified-SAT certificate did not replay".to_owned()),
            Err(error) => Err(error.to_string()),
        }
    }

    fn render_artifact(
        args: &Args,
        s: &Summary,
        instances: &[JsonValue],
        identity: &ArtifactIdentity<'_>,
    ) -> Result<String, String> {
        let artifact = json!({
            "version": ARTIFACT_VERSION,
            "config": artifact_config_record(args, identity),
            "summary": artifact_summary_record(args, s, identity.compare_backend_name),
            "triage": artifact_triage_record(s, instances),
            "instances": instances,
        });
        serde_json::to_string_pretty(&artifact).map_err(|e| format!("render artifact: {e}"))
    }

    fn artifact_config_record(args: &Args, identity: &ArtifactIdentity<'_>) -> JsonValue {
        let manifest = identity.corpus_manifest;
        json!({
            "corpus": args.dir.display().to_string(),
            "corpus_source": args.corpus_source.as_deref().or_else(|| {
                manifest.map(|value| value.source.as_str())
            }),
            "corpus_hash": identity.corpus_hash,
            "corpus_manifest": corpus_manifest_record(manifest),
            "config_hash": identity.config_hash,
            "logic": args.logic.as_deref().or_else(|| {
                manifest.map(|value| value.logic.as_str())
            }),
            "selected_families": optional_strings(&args.families),
            "timeout_ms": args.timeout_ms,
            "jobs": usize_to_u64(args.jobs),
            "resource_limit": optional_u64(args.resource_limit),
            "node_budget": optional_u64(args.node_budget),
            "cnf_variable_budget": optional_u64(args.cnf_variable_budget),
            "cnf_clause_budget": optional_u64(args.cnf_clause_budget),
            "cnf_inprocessing": args.cnf_inprocessing,
            "cnf_vivify": args.cnf_vivify,
            "native_cdcl": args.native_cdcl,
            "prove_unsat": args.prove_unsat,
            "preprocess": args.preprocess,
            "limit": optional_limit(args.limit),
            "backend": identity.backend_name,
            "backend_kind": args.backend.as_str(),
            "compare_backend": identity.compare_backend_name,
            "compare_z3": args.compare_z3,
            "require_in_process_z3": args.require_in_process_z3,
            "require_reproducible_run": args.require_reproducible_run,
            "require_deterministic_resources": args.require_deterministic_resources,
            "min_decided_percent": args.min_decided_percent,
            "query_plan": {
                "mode": args.query_plan.as_str(),
                "sat_replay_failure_policy": sat_replay_policy_name(args.query_plan),
                "refine_rounds": usize_to_u64(args.refine_rounds),
                "refine_batch": usize_to_u64(args.refine_batch),
                "refine_adaptive_batch": args.refine_adaptive_batch,
                "refine_select": args.refine_select.as_str(),
            },
            "harness": format!("axeyum-bench {}", env!("CARGO_PKG_VERSION")),
            "determinism": determinism_record(),
            "resources": resource_profile_record(args),
            "rewrite": rewrite_config(args.rewrite),
            "experiment": experiment_identity_record(identity.experiment),
        })
    }

    fn artifact_summary_record(
        args: &Args,
        s: &Summary,
        compare_backend_name: Option<&str>,
    ) -> JsonValue {
        json!({
            "files": s.files,
            "sat": s.sat,
            "unsat": s.unsat,
            "unknown": s.unknown,
            "unsupported": s.unsupported,
            "errors": s.errors,
            "decided": s.sat + s.unsat,
            "decided_percent": decided_percent(s),
            "agree": s.agree,
            "disagree": s.disagree,
            "model_replay_failures": s.model_replay_failures,
            "unsat_proof_replay": {
                "requested": args.prove_unsat,
                "checked": s.unsat_proof_replay_checked,
                "missing": s.unsat_proof_replay_missing,
                "check_time_s": s.unsat_proof_replay_s,
                "check_time": timing_distribution_record(
                    &s.unsat_proof_replay_samples,
                    |seconds| seconds,
                ),
                "timing_accounting": "nested within SAT solve time; not added again to cold total",
            },
            "manifest": {
                "expected": s.manifest_expected,
                "compared": s.manifest_compared,
                "agree": s.manifest_agree,
                "disagree": s.manifest_disagree,
            },
            "par2_mean_s": s.par2_seconds / decided_denominator(s),
            "blocker_buckets": s.blocker_buckets,
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
            "query_shape": query_shape_summary_record(s),
            "client_comparison": client_comparison_record(s),
        })
    }

    fn artifact_triage_record(s: &Summary, instances: &[JsonValue]) -> JsonValue {
        json!({
            "unsupported": triage(instances, &["unsupported"]),
            "errors": triage(
                instances,
                &["read-error", "parse-error", "solver-error", "model-replay-error"]
            ),
            "rewrite_decision_changes": rewrite_decision_changes(instances),
            "soundness": {
                "status_disagreements": s.disagree,
                "model_replay_failures": s.model_replay_failures,
                "unsat_proof_replay_missing": s.unsat_proof_replay_missing,
                "rewrite_sat_unsat_conflicts": s.rewrite_sat_unsat_conflicts,
                "oracle_disagreements": s.oracle_disagree,
                "manifest_disagreements": s.manifest_disagree,
            },
        })
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

    fn corpus_manifest_record(manifest: Option<&CorpusManifestSelection>) -> JsonValue {
        manifest.map_or(JsonValue::Null, |manifest| {
            json!({
                "schema_version": CORPUS_MANIFEST_VERSION,
                "path": manifest.manifest_path.display().to_string(),
                "content_hash": manifest.manifest_hash,
                "name": manifest.name,
                "source": manifest.source,
                "logic": manifest.logic,
                "total_entries": manifest.total_entries,
                "selected_tier": manifest.selected_tier,
                "selected_entries": manifest.entries.len(),
                "selected_family_counts": manifest_family_counts(&manifest.entries),
                "selected_tier_counts": manifest_tier_counts(&manifest.entries),
                "membership": "exact: every .smt2 file under the corpus root is manifested",
            })
        })
    }

    fn determinism_record() -> JsonValue {
        let batsat = rustsat_batsat_determinism();
        json!({
            "profile": DETERMINISM_PROFILE,
            "corpus_order": "stable manifest order (or deterministic lexical path order without a manifest)",
            "sat_bv": {
                "adapter": "rustsat-batsat",
                "option_source": "batsat::SolverOpts::default from the Cargo.lock-pinned dependency",
                "random_seed": batsat.random_seed,
                "random_var_freq": batsat.random_var_freq,
                "random_polarity": batsat.random_polarity,
                "random_initial_activity": batsat.random_initial_activity,
            },
            "z3": z3_determinism_record(),
        })
    }

    fn resource_profile_record(args: &Args) -> JsonValue {
        let primary_search_unit = if args.native_cdcl || args.prove_unsat {
            "native proof-CDCL conflicts"
        } else {
            "rustsat-batsat within_budget progress checks"
        };
        json!({
            "profile": args.require_deterministic_resources.then_some(RESOURCE_PROFILE),
            "required": args.require_deterministic_resources,
            "limits": {
                "search": optional_u64(args.resource_limit),
                "dag_nodes": optional_u64(args.node_budget),
                "cnf_variables": optional_u64(args.cnf_variable_budget),
                "cnf_clauses": optional_u64(args.cnf_clause_budget),
            },
            "units": {
                "primary_search": primary_search_unit,
                "z3_oracle_search": args.compare_z3.then_some("Z3 rlimit units"),
                "dag_nodes": "unique reachable term DAG nodes before lowering",
                "cnf_variables": "variables in the formula submitted to SAT",
                "cnf_clauses": "clauses in the formula submitted to SAT",
            },
            "wall_clock_safety_timeout_ms": args.timeout_ms,
            "wall_clock_is_deterministic": false,
            "cross_backend_numeric_limits_are_work_equivalent": false,
        })
    }

    #[cfg(feature = "z3")]
    fn z3_determinism_record() -> JsonValue {
        json!({
            "random_seed": DETERMINISTIC_Z3_RANDOM_SEED,
            "parameter": "random_seed",
            "set_explicitly": true,
        })
    }

    #[cfg(not(feature = "z3"))]
    fn z3_determinism_record() -> JsonValue {
        JsonValue::Null
    }

    fn manifest_family_counts(entries: &[CorpusManifestEntry]) -> BTreeMap<String, u64> {
        let mut counts = BTreeMap::new();
        for entry in entries {
            *counts.entry(entry.family.clone()).or_insert(0) += 1;
        }
        counts
    }

    fn manifest_tier_counts(entries: &[CorpusManifestEntry]) -> BTreeMap<String, u64> {
        let mut counts = BTreeMap::new();
        for entry in entries {
            for tier in &entry.tiers {
                *counts.entry(tier.clone()).or_insert(0) += 1;
            }
        }
        counts
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

    fn optional_u64(value: Option<u64>) -> JsonValue {
        value.map_or(JsonValue::Null, |value| json!(value))
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

    fn duration_ms_f64(duration: Duration) -> f64 {
        duration.as_secs_f64() * 1000.0
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

    impl ExperimentIdentity {
        fn collect(backend: &str, compare_backend: Option<&str>) -> Self {
            let root = repository_root();
            let source_revision = command_output("git", &["rev-parse", "HEAD"], &root);
            let source_dirty = command_output(
                "git",
                &[
                    "status",
                    "--porcelain=v1",
                    "--untracked-files=all",
                    "--",
                    ".",
                    ":(exclude)bench-results/**",
                ],
                &root,
            )
            .map(|output| !output.is_empty());
            let cargo_lock_hash = fs::read(root.join("Cargo.lock"))
                .ok()
                .map(|bytes| content_hash(&bytes));
            let rustc_program = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
            let cargo_program = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_owned());
            let rustc = command_output(&rustc_program, &["--version", "--verbose"], &root);
            let cargo = command_output(&cargo_program, &["--version"], &root);
            let hardware = HardwareIdentity::collect();
            let mut identity = Self {
                source_revision,
                source_dirty,
                cargo_lock_hash,
                rustc,
                cargo,
                build_profile: if cfg!(debug_assertions) {
                    "debug".to_owned()
                } else {
                    "release".to_owned()
                },
                backend: backend.to_owned(),
                compare_backend: compare_backend.map(str::to_owned),
                hardware,
                environment_hash: String::new(),
            };
            identity.environment_hash = identity.compute_environment_hash();
            identity
        }

        fn compute_environment_hash(&self) -> String {
            let mut fields = vec![
                self.cargo_lock_hash.as_deref().unwrap_or("missing"),
                self.rustc.as_deref().unwrap_or("missing"),
                self.cargo.as_deref().unwrap_or("missing"),
                self.build_profile.as_str(),
                self.backend.as_str(),
                self.compare_backend.as_deref().unwrap_or("none"),
                self.hardware.os.as_str(),
                self.hardware.arch.as_str(),
                self.hardware.cpu_model.as_deref().unwrap_or("missing"),
                self.hardware.kernel.as_deref().unwrap_or("missing"),
            ];
            let parallelism = self.hardware.parallelism.to_string();
            let memory = self
                .hardware
                .total_memory_bytes
                .map_or_else(|| "missing".to_owned(), |bytes| bytes.to_string());
            fields.push(&parallelism);
            fields.push(&memory);
            content_hash(fields.join("\0").as_bytes())
        }

        fn require_reproducible(&self) -> Result<(), String> {
            let mut missing = Vec::new();
            if self.source_revision.is_none() {
                missing.push("source revision");
            }
            match self.source_dirty {
                Some(false) => {}
                Some(true) => missing.push("clean source tree (source changes are present)"),
                None => missing.push("clean source tree status"),
            }
            if self.cargo_lock_hash.is_none() {
                missing.push("Cargo.lock hash");
            }
            if self.rustc.is_none() {
                missing.push("rustc version");
            }
            if self.cargo.is_none() {
                missing.push("cargo version");
            }
            if self.hardware.cpu_model.is_none() {
                missing.push("CPU model");
            }
            if self.hardware.kernel.is_none() {
                missing.push("kernel version");
            }
            if self.hardware.total_memory_bytes.is_none() {
                missing.push("total memory");
            }
            if missing.is_empty() {
                Ok(())
            } else {
                Err(format!(
                    "`--require-reproducible-run` identity gate failed: {}",
                    missing.join(", ")
                ))
            }
        }
    }

    impl HardwareIdentity {
        fn collect() -> Self {
            let parallelism =
                std::thread::available_parallelism().map_or(1, std::num::NonZero::get);
            let cpuinfo = fs::read_to_string("/proc/cpuinfo").ok();
            let meminfo = fs::read_to_string("/proc/meminfo").ok();
            let cpu_model = cpuinfo
                .as_deref()
                .and_then(parse_cpu_model)
                .or_else(|| {
                    command_output(
                        "sysctl",
                        &["-n", "machdep.cpu.brand_string"],
                        Path::new("."),
                    )
                })
                .or_else(|| command_output("sysctl", &["-n", "hw.model"], Path::new(".")));
            let total_memory_bytes = meminfo
                .as_deref()
                .and_then(parse_total_memory_bytes)
                .or_else(|| {
                    command_output("sysctl", &["-n", "hw.memsize"], Path::new("."))
                        .and_then(|value| value.parse().ok())
                });
            Self {
                os: std::env::consts::OS.to_owned(),
                arch: std::env::consts::ARCH.to_owned(),
                parallelism: usize_to_u64(parallelism),
                cpu_model,
                kernel: command_output("uname", &["-srmo"], Path::new(".")),
                total_memory_bytes,
            }
        }
    }

    fn repository_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn command_output(program: &str, args: &[&str], cwd: &Path) -> Option<String> {
        let output = Command::new(program)
            .args(args)
            .current_dir(cwd)
            .output()
            .ok()?;
        if !output.status.success() {
            return None;
        }
        let value = String::from_utf8(output.stdout).ok()?;
        Some(value.trim().to_owned())
    }

    fn parse_cpu_model(cpuinfo: &str) -> Option<String> {
        for key in ["model name", "Hardware", "Processor"] {
            if let Some(value) = cpuinfo.lines().find_map(|line| {
                let (name, value) = line.split_once(':')?;
                (name.trim() == key)
                    .then(|| value.trim())
                    .filter(|value| !value.is_empty())
            }) {
                return Some(value.to_owned());
            }
        }
        None
    }

    fn parse_total_memory_bytes(meminfo: &str) -> Option<u64> {
        let line = meminfo.lines().find(|line| line.starts_with("MemTotal:"))?;
        let mut fields = line.split_ascii_whitespace();
        (fields.next()? == "MemTotal:").then_some(())?;
        let kib = fields.next()?.parse::<u64>().ok()?;
        (fields.next()? == "kB").then_some(())?;
        kib.checked_mul(1024)
    }

    fn experiment_identity_record(identity: &ExperimentIdentity) -> JsonValue {
        json!({
            "source": {
                "revision": identity.source_revision,
                "dirty": identity.source_dirty,
                "dirty_scope": "repository excluding bench-results/**",
            },
            "toolchain": {
                "rustc": identity.rustc,
                "cargo": identity.cargo,
                "build_profile": identity.build_profile,
                "cargo_lock_hash": identity.cargo_lock_hash,
            },
            "solvers": {
                "backend": identity.backend,
                "compare_backend": identity.compare_backend,
            },
            "hardware": {
                "os": identity.hardware.os,
                "arch": identity.hardware.arch,
                "parallelism": identity.hardware.parallelism,
                "cpu_model": identity.hardware.cpu_model,
                "kernel": identity.hardware.kernel,
                "total_memory_bytes": identity.hardware.total_memory_bytes,
            },
            "environment_hash": identity.environment_hash,
            "comparison_contract": "compare config_hash + environment_hash; source revision identifies the tested commit and may differ",
        })
    }

    fn fingerprint_config(
        args: &Args,
        backend_name: &str,
        corpus_hash: &str,
        corpus_manifest: Option<&CorpusManifestSelection>,
    ) -> String {
        let mut hash = FNV_OFFSET;
        update_hash(&mut hash, &ARTIFACT_VERSION.to_le_bytes());
        update_hash(&mut hash, args.dir.display().to_string().as_bytes());
        update_hash(&mut hash, &args.timeout_ms.to_le_bytes());
        update_hash(&mut hash, &usize_to_u64(args.jobs).to_le_bytes());
        update_hash(&mut hash, &usize_to_u64(args.limit).to_le_bytes());
        let effective_source = args
            .corpus_source
            .as_deref()
            .or_else(|| corpus_manifest.map(|manifest| manifest.source.as_str()));
        update_hash(&mut hash, effective_source.unwrap_or("").as_bytes());
        if let Some(manifest) = corpus_manifest {
            update_hash(&mut hash, manifest.manifest_hash.as_bytes());
        }
        update_hash(
            &mut hash,
            args.corpus_tier.as_deref().unwrap_or("").as_bytes(),
        );
        let effective_logic = args
            .logic
            .as_deref()
            .or_else(|| corpus_manifest.map(|manifest| manifest.logic.as_str()));
        update_hash(&mut hash, effective_logic.unwrap_or("").as_bytes());
        for family in &args.families {
            update_hash(&mut hash, family.as_bytes());
            update_hash(&mut hash, &[0]);
        }
        let batsat = rustsat_batsat_determinism();
        update_hash(&mut hash, DETERMINISM_PROFILE.as_bytes());
        update_hash(&mut hash, &batsat.random_seed.to_bits().to_le_bytes());
        update_hash(&mut hash, &batsat.random_var_freq.to_bits().to_le_bytes());
        update_hash(&mut hash, &[u8::from(batsat.random_polarity)]);
        update_hash(&mut hash, &[u8::from(batsat.random_initial_activity)]);
        #[cfg(feature = "z3")]
        update_hash(&mut hash, &DETERMINISTIC_Z3_RANDOM_SEED.to_le_bytes());
        update_hash(&mut hash, args.rewrite.as_str().as_bytes());
        update_hash(&mut hash, args.backend.as_str().as_bytes());
        update_hash(&mut hash, args.query_plan.as_str().as_bytes());
        update_hash(&mut hash, &usize_to_u64(args.refine_rounds).to_le_bytes());
        update_hash(&mut hash, &usize_to_u64(args.refine_batch).to_le_bytes());
        update_hash(&mut hash, &[u8::from(args.refine_adaptive_batch)]);
        update_hash(&mut hash, args.refine_select.as_str().as_bytes());
        update_hash(
            &mut hash,
            &args.resource_limit.unwrap_or(u64::MAX).to_le_bytes(),
        );
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
        update_hash(&mut hash, &[u8::from(args.native_cdcl)]);
        update_hash(&mut hash, &[u8::from(args.prove_unsat)]);
        update_hash(&mut hash, &[u8::from(args.preprocess)]);
        update_hash(&mut hash, &[u8::from(args.compare_z3)]);
        update_hash(&mut hash, &[u8::from(args.require_in_process_z3)]);
        update_hash(&mut hash, &[u8::from(args.require_reproducible_run)]);
        update_hash(&mut hash, &[u8::from(args.require_deterministic_resources)]);
        update_hash(
            &mut hash,
            &args
                .min_decided_percent
                .map_or_else(|| "none".to_owned(), |percent| percent.to_string())
                .into_bytes(),
        );
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

    fn content_hash(bytes: &[u8]) -> String {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let digest = Sha256::digest(bytes);
        let mut encoded = String::with_capacity(CONTENT_HASH_PREFIX.len() + digest.len() * 2);
        encoded.push_str(CONTENT_HASH_PREFIX);
        for byte in digest {
            encoded.push(char::from(HEX[usize::from(byte >> 4)]));
            encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
        }
        encoded
    }

    /// Turn the shadow-diff exporter's small metadata index into the immutable
    /// manifest consumed by benchmark runs. The producer owns semantic facts
    /// (`expected`, `family`, and tier membership); this side owns byte identity
    /// and exact-directory validation, so a capture cannot accidentally ship a
    /// stale digest or omit a query that is present on disk.
    fn generate_corpus_manifest(
        root: &Path,
        index_path: &Path,
        output_path: &Path,
    ) -> Result<(), String> {
        if index_path == output_path {
            return Err(
                "capture index and generated corpus manifest must use different paths".to_owned(),
            );
        }
        let index_bytes = fs::read(index_path)
            .map_err(|error| format!("read capture index {}: {error}", index_path.display()))?;
        let manifest_bytes =
            render_corpus_manifest_from_capture_index(root, index_path, &index_bytes, output_path)?;
        fs::write(output_path, manifest_bytes).map_err(|error| {
            format!(
                "write generated corpus manifest {}: {error}",
                output_path.display()
            )
        })
    }

    fn render_corpus_manifest_from_capture_index(
        root: &Path,
        index_path: &Path,
        bytes: &[u8],
        generated_path: &Path,
    ) -> Result<Vec<u8>, String> {
        let value: JsonValue = serde_json::from_slice(bytes)
            .map_err(|error| format!("parse capture index {}: {error}", index_path.display()))?;
        let object = value
            .as_object()
            .ok_or_else(|| "capture index root must be a JSON object".to_owned())?;
        validate_capture_index_keys(
            object,
            &["version", "name", "source", "logic", "files"],
            "root",
        )?;
        let version = object
            .get("version")
            .and_then(JsonValue::as_u64)
            .ok_or_else(|| "capture index `version` must be an unsigned integer".to_owned())?;
        if version != CORPUS_MANIFEST_VERSION {
            return Err(format!(
                "unsupported capture index version {version}; expected {CORPUS_MANIFEST_VERSION}"
            ));
        }
        let name = required_capture_index_string(object, "name")?;
        let source = required_capture_index_string(object, "source")?;
        let logic = required_capture_index_string(object, "logic")?;
        let file_values = object
            .get("files")
            .and_then(JsonValue::as_array)
            .ok_or_else(|| "capture index `files` must be an array".to_owned())?;
        if file_values.is_empty() {
            return Err("capture index `files` must not be empty".to_owned());
        }

        let mut paths = BTreeSet::new();
        let mut entries = Vec::with_capacity(file_values.len());
        for (index, value) in file_values.iter().enumerate() {
            let entry = parse_capture_index_entry(root, index, value)?;
            if !paths.insert(entry.path.clone()) {
                return Err(format!("duplicate capture index path `{}`", entry.path));
            }
            entries.push(entry);
        }
        validate_manifest_membership(root, &entries)
            .map_err(|error| error.replacen("corpus manifest", "capture index", 1))?;

        let files = entries
            .iter()
            .map(|entry| {
                json!({
                    "path": entry.path,
                    "content_hash": entry.content_hash,
                    "expected": entry.expected,
                    "family": entry.family,
                    "tiers": entry.tiers,
                })
            })
            .collect::<Vec<_>>();
        let manifest = json!({
            "version": CORPUS_MANIFEST_VERSION,
            "name": name,
            "source": source,
            "logic": logic,
            "files": files,
        });
        let mut rendered = serde_json::to_vec_pretty(&manifest)
            .map_err(|error| format!("serialize generated corpus manifest: {error}"))?;
        rendered.push(b'\n');

        // Exercise the exact benchmark ingestion path before writing anything.
        // This also protects the generator and consumer from schema drift.
        parse_corpus_manifest(root, generated_path, &rendered, None)?;
        Ok(rendered)
    }

    fn parse_capture_index_entry(
        root: &Path,
        index: usize,
        value: &JsonValue,
    ) -> Result<CorpusManifestEntry, String> {
        let object = value
            .as_object()
            .ok_or_else(|| format!("capture index files[{index}] must be an object"))?;
        validate_capture_index_keys(
            object,
            &["path", "expected", "family", "tiers"],
            &format!("files[{index}]"),
        )?;
        let path = required_capture_index_string(object, "path")?;
        validate_manifest_path(&path)?;
        let expected = required_capture_index_string(object, "expected")?;
        if !matches!(expected.as_str(), "sat" | "unsat") {
            return Err(format!(
                "capture index `{path}` expected verdict must be `sat` or `unsat`"
            ));
        }
        let family = required_capture_index_string(object, "family")?;
        validate_manifest_label(&family, &format!("family for `{path}`"))?;
        let tiers = required_capture_index_string_array(object, "tiers")?;
        validate_manifest_tiers(&path, &tiers)?;
        let file_path = root.join(&path);
        let file_bytes = fs::read(&file_path)
            .map_err(|error| format!("read captured query {}: {error}", file_path.display()))?;
        Ok(CorpusManifestEntry {
            path,
            content_hash: content_hash(&file_bytes),
            expected,
            family,
            tiers,
        })
    }

    fn validate_capture_index_keys(
        object: &serde_json::Map<String, JsonValue>,
        allowed: &[&str],
        location: &str,
    ) -> Result<(), String> {
        if let Some(key) = object.keys().find(|key| !allowed.contains(&key.as_str())) {
            return Err(format!(
                "capture index {location} contains unknown field `{key}`"
            ));
        }
        Ok(())
    }

    fn required_capture_index_string(
        object: &serde_json::Map<String, JsonValue>,
        field: &str,
    ) -> Result<String, String> {
        required_manifest_string(object, field)
            .map_err(|error| error.replacen("corpus manifest", "capture index", 1))
    }

    fn required_capture_index_string_array(
        object: &serde_json::Map<String, JsonValue>,
        field: &str,
    ) -> Result<Vec<String>, String> {
        required_manifest_string_array(object, field)
            .map_err(|error| error.replacen("corpus manifest", "capture index", 1))
    }

    fn load_corpus(args: &Args) -> Result<CorpusSelection, String> {
        let Some(manifest_path) = &args.corpus_manifest else {
            return Ok(CorpusSelection {
                files: collect_smt2(&args.dir, args.limit),
                manifest: None,
            });
        };
        let bytes = fs::read(manifest_path).map_err(|error| {
            format!("read corpus manifest {}: {error}", manifest_path.display())
        })?;
        let manifest = parse_corpus_manifest(
            &args.dir,
            manifest_path,
            &bytes,
            args.corpus_tier.as_deref(),
        )?;
        if let Some(source) = &args.corpus_source
            && source != &manifest.source
        {
            return Err(format!(
                "corpus source `{source}` conflicts with manifest source `{}`",
                manifest.source
            ));
        }
        if let Some(logic) = &args.logic
            && logic != &manifest.logic
        {
            return Err(format!(
                "logic `{logic}` conflicts with manifest logic `{}`",
                manifest.logic
            ));
        }
        let files = manifest
            .entries
            .iter()
            .map(|entry| args.dir.join(&entry.path))
            .collect();
        Ok(CorpusSelection {
            files,
            manifest: Some(manifest),
        })
    }

    fn parse_corpus_manifest(
        root: &Path,
        manifest_path: &Path,
        bytes: &[u8],
        selected_tier: Option<&str>,
    ) -> Result<CorpusManifestSelection, String> {
        if let Some(tier) = selected_tier {
            validate_manifest_label(tier, "selected tier")?;
        }
        let value: JsonValue = serde_json::from_slice(bytes).map_err(|error| {
            format!("parse corpus manifest {}: {error}", manifest_path.display())
        })?;
        let object = value
            .as_object()
            .ok_or_else(|| "corpus manifest root must be a JSON object".to_owned())?;
        let version = object
            .get("version")
            .and_then(JsonValue::as_u64)
            .ok_or_else(|| "corpus manifest `version` must be an unsigned integer".to_owned())?;
        if version != CORPUS_MANIFEST_VERSION {
            return Err(format!(
                "unsupported corpus manifest version {version}; expected {CORPUS_MANIFEST_VERSION}"
            ));
        }
        let name = required_manifest_string(object, "name")?;
        let source = required_manifest_string(object, "source")?;
        let logic = required_manifest_string(object, "logic")?;
        let file_values = object
            .get("files")
            .and_then(JsonValue::as_array)
            .ok_or_else(|| "corpus manifest `files` must be an array".to_owned())?;
        if file_values.is_empty() {
            return Err("corpus manifest `files` must not be empty".to_owned());
        }

        let all_entries = parse_manifest_entries(root, file_values)?;
        validate_manifest_membership(root, &all_entries)?;

        let entries = all_entries
            .iter()
            .filter(|entry| {
                selected_tier
                    .is_none_or(|tier| entry.tiers.iter().any(|entry_tier| entry_tier == tier))
            })
            .cloned()
            .collect::<Vec<_>>();
        if entries.is_empty() {
            return Err(format!(
                "corpus manifest tier `{}` selects no files",
                selected_tier.unwrap_or("all")
            ));
        }
        Ok(CorpusManifestSelection {
            manifest_path: manifest_path.to_path_buf(),
            manifest_hash: content_hash(bytes),
            name,
            source,
            logic,
            total_entries: all_entries.len(),
            selected_tier: selected_tier.map(str::to_owned),
            entries,
        })
    }

    fn parse_manifest_entries(
        root: &Path,
        values: &[JsonValue],
    ) -> Result<Vec<CorpusManifestEntry>, String> {
        let mut entries = Vec::with_capacity(values.len());
        let mut paths = BTreeSet::new();
        for (index, value) in values.iter().enumerate() {
            let entry = parse_manifest_entry(root, index, value)?;
            if !paths.insert(entry.path.clone()) {
                return Err(format!("duplicate corpus manifest path `{}`", entry.path));
            }
            entries.push(entry);
        }
        Ok(entries)
    }

    fn parse_manifest_entry(
        root: &Path,
        index: usize,
        value: &JsonValue,
    ) -> Result<CorpusManifestEntry, String> {
        let object = value
            .as_object()
            .ok_or_else(|| format!("corpus manifest files[{index}] must be an object"))?;
        let path = required_manifest_string(object, "path")?;
        validate_manifest_path(&path)?;
        let expected = required_manifest_string(object, "expected")?;
        if !matches!(expected.as_str(), "sat" | "unsat") {
            return Err(format!(
                "corpus manifest `{path}` expected verdict must be `sat` or `unsat`"
            ));
        }
        let family = required_manifest_string(object, "family")?;
        validate_manifest_label(&family, &format!("family for `{path}`"))?;
        let tiers = required_manifest_string_array(object, "tiers")?;
        validate_manifest_tiers(&path, &tiers)?;
        let declared_hash = required_manifest_string(object, "content_hash")?;
        validate_declared_content_hash(&declared_hash, &path)?;
        let file_path = root.join(&path);
        let file_bytes = fs::read(&file_path)
            .map_err(|error| format!("read manifested query {}: {error}", file_path.display()))?;
        let actual_hash = content_hash(&file_bytes);
        if declared_hash != actual_hash {
            return Err(format!(
                "corpus manifest hash mismatch for `{path}`: declared `{declared_hash}`, actual `{actual_hash}`"
            ));
        }
        Ok(CorpusManifestEntry {
            path,
            content_hash: declared_hash,
            expected,
            family,
            tiers,
        })
    }

    fn validate_manifest_tiers(path: &str, tiers: &[String]) -> Result<(), String> {
        if tiers.is_empty() {
            return Err(format!(
                "corpus manifest `{path}` must name at least one tier"
            ));
        }
        let mut unique = BTreeSet::new();
        for tier in tiers {
            validate_manifest_label(tier, &format!("tier for `{path}`"))?;
            if !unique.insert(tier) {
                return Err(format!("corpus manifest `{path}` repeats tier `{tier}`"));
            }
        }
        Ok(())
    }

    fn validate_manifest_membership(
        root: &Path,
        entries: &[CorpusManifestEntry],
    ) -> Result<(), String> {
        let manifested = entries
            .iter()
            .map(|entry| entry.path.clone())
            .collect::<BTreeSet<_>>();
        let disk = collect_smt2_checked(root)?
            .iter()
            .map(|path| manifest_relative_path(root, path))
            .collect::<Result<BTreeSet<_>, _>>()?;
        if disk == manifested {
            return Ok(());
        }
        let missing = manifested.difference(&disk).cloned().collect::<Vec<_>>();
        let unlisted = disk.difference(&manifested).cloned().collect::<Vec<_>>();
        Err(format!(
            "corpus manifest membership mismatch: missing={missing:?}, unlisted={unlisted:?}"
        ))
    }

    fn required_manifest_string(
        object: &serde_json::Map<String, JsonValue>,
        field: &str,
    ) -> Result<String, String> {
        let value = object
            .get(field)
            .and_then(JsonValue::as_str)
            .ok_or_else(|| format!("corpus manifest `{field}` must be a string"))?;
        if value.is_empty() {
            return Err(format!("corpus manifest `{field}` must not be empty"));
        }
        Ok(value.to_owned())
    }

    fn required_manifest_string_array(
        object: &serde_json::Map<String, JsonValue>,
        field: &str,
    ) -> Result<Vec<String>, String> {
        object
            .get(field)
            .and_then(JsonValue::as_array)
            .ok_or_else(|| format!("corpus manifest `{field}` must be an array"))?
            .iter()
            .enumerate()
            .map(|(index, value)| {
                value
                    .as_str()
                    .map(str::to_owned)
                    .ok_or_else(|| format!("corpus manifest `{field}`[{index}] must be a string"))
            })
            .collect()
    }

    fn validate_manifest_path(path: &str) -> Result<(), String> {
        let valid_segments = !path.is_empty()
            && !path.contains('\\')
            && path
                .split('/')
                .all(|segment| !segment.is_empty() && segment != "." && segment != "..");
        if !valid_segments || Path::new(path).is_absolute() {
            return Err(format!(
                "corpus manifest path `{path}` must be a normalized relative `/`-separated path"
            ));
        }
        if Path::new(path)
            .extension()
            .is_none_or(|extension| extension != "smt2")
        {
            return Err(format!("corpus manifest path `{path}` must end in `.smt2`"));
        }
        Ok(())
    }

    fn validate_manifest_label(value: &str, what: &str) -> Result<(), String> {
        if value.is_empty()
            || !value
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
        {
            return Err(format!(
                "corpus manifest {what} `{value}` must use only ASCII letters, digits, `.`, `_`, or `-`"
            ));
        }
        Ok(())
    }

    fn validate_declared_content_hash(hash: &str, path: &str) -> Result<(), String> {
        let Some(digest) = hash.strip_prefix(CONTENT_HASH_PREFIX) else {
            return Err(format!(
                "corpus manifest `{path}` content_hash must start with `{CONTENT_HASH_PREFIX}`"
            ));
        };
        if digest.len() != 64
            || !digest
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(format!(
                "corpus manifest `{path}` content_hash must contain exactly 64 lowercase hexadecimal digits"
            ));
        }
        Ok(())
    }

    fn manifest_relative_path(root: &Path, path: &Path) -> Result<String, String> {
        let relative = path.strip_prefix(root).map_err(|error| {
            format!(
                "query path {} is not below corpus root {}: {error}",
                path.display(),
                root.display()
            )
        })?;
        let value = relative.to_string_lossy().replace('\\', "/");
        validate_manifest_path(&value)?;
        Ok(value)
    }

    fn collect_smt2_checked(dir: &Path) -> Result<Vec<PathBuf>, String> {
        let mut files = Vec::new();
        let mut dirs = vec![dir.to_path_buf()];
        while let Some(current) = dirs.pop() {
            let entries = fs::read_dir(&current)
                .map_err(|error| format!("read corpus directory {}: {error}", current.display()))?;
            for entry in entries {
                let entry = entry.map_err(|error| {
                    format!(
                        "read corpus directory entry in {}: {error}",
                        current.display()
                    )
                })?;
                let path = entry.path();
                if path.is_dir() {
                    dirs.push(path);
                } else if path
                    .extension()
                    .is_some_and(|extension| extension == "smt2")
                {
                    files.push(path);
                }
            }
        }
        files.sort();
        Ok(files)
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

        fn micro_corpus_root() -> PathBuf {
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../corpus/micro")
        }

        fn micro_manifest_value() -> JsonValue {
            let root = micro_corpus_root();
            let entries = [
                (
                    "sat-add.smt2",
                    "sat",
                    "arithmetic",
                    vec!["representative", "full"],
                ),
                ("sat-quoted-symbol.smt2", "sat", "symbols", vec!["full"]),
                (
                    "unsat-ult-zero.smt2",
                    "unsat",
                    "comparison",
                    vec!["representative", "full"],
                ),
            ]
            .map(|(path, expected, family, tiers)| {
                let bytes = fs::read(root.join(path)).unwrap();
                json!({
                    "path": path,
                    "content_hash": content_hash(&bytes),
                    "expected": expected,
                    "family": family,
                    "tiers": tiers,
                })
            });
            json!({
                "version": CORPUS_MANIFEST_VERSION,
                "name": "micro-manifest-test",
                "source": "committed micro corpus; ingestion contract test only",
                "logic": "QF_BV",
                "files": entries,
            })
        }

        fn micro_capture_index_value() -> JsonValue {
            let mut value = micro_manifest_value();
            for entry in value["files"].as_array_mut().unwrap() {
                entry.as_object_mut().unwrap().remove("content_hash");
            }
            value
        }

        #[test]
        fn blocker_buckets_categorize_undecided_by_root_cause() {
            fn rec(outcome: &'static str, detail: Option<&str>) -> SolveRecord {
                SolveRecord {
                    outcome,
                    detail: detail.map(str::to_owned),
                    stats: SolveStats::default(),
                    model_replay: Duration::ZERO,
                    model_replay_failure: false,
                }
            }
            let mut s = Summary::default();
            // unknowns carry the UnknownKind as the detail prefix ("Kind: …").
            accumulate_primary(&rec("unknown", Some("Timeout: ran out of time")), &mut s);
            accumulate_primary(&rec("unknown", Some("Timeout: ran out of time")), &mut s);
            accumulate_primary(&rec("unknown", Some("EncodingBudget: too big")), &mut s);
            accumulate_primary(&rec("unsupported", Some("arrays")), &mut s);
            accumulate_primary(&rec("sat", None), &mut s); // decided → not a blocker
            accumulate_primary(&rec("unsat", None), &mut s);

            assert_eq!(s.blocker_buckets.get("unknown:Timeout"), Some(&2));
            assert_eq!(s.blocker_buckets.get("unknown:EncodingBudget"), Some(&1));
            assert_eq!(s.blocker_buckets.get("unsupported"), Some(&1));
            assert_eq!(s.blocker_buckets.len(), 3, "sat/unsat are not blockers");
            // Leaderboard ranks most-frequent first (ties by key).
            assert_eq!(
                blocker_leaderboard(&s.blocker_buckets),
                "unknown:Timeout=2 unknown:EncodingBudget=1 unsupported=1"
            );
        }

        #[test]
        fn decided_rate_and_operational_errors_are_benchmark_gates() {
            let mostly_failed = Summary {
                files: 100,
                sat: 1,
                unsat: 1,
                errors: 98,
                ..Summary::default()
            };
            assert!((decided_percent(&mostly_failed) - 2.0).abs() < f64::EPSILON);
            assert_eq!(
                report_summary(&mostly_failed, None, false),
                ExitCode::FAILURE,
                "fast operational failure must never pass as a benchmark result"
            );

            let incomplete = Summary {
                files: 10,
                sat: 4,
                unsat: 4,
                unknown: 2,
                ..Summary::default()
            };
            assert_eq!(
                report_summary(&incomplete, Some(80.0), false),
                ExitCode::SUCCESS
            );
            assert_eq!(
                report_summary(&incomplete, Some(80.1), false),
                ExitCode::FAILURE
            );
        }

        #[test]
        fn complete_in_process_z3_comparison_is_a_client_gate() {
            let complete = Summary {
                files: 2,
                sat: 1,
                unsat: 1,
                client_comparison_files: 2,
                ..Summary::default()
            };
            assert_eq!(
                report_summary(&complete, Some(100.0), true),
                ExitCode::SUCCESS
            );

            let partial = Summary {
                client_comparison_files: 1,
                ..complete
            };
            assert_eq!(
                report_summary(&partial, Some(100.0), true),
                ExitCode::FAILURE
            );
        }

        #[test]
        fn decided_rate_threshold_parser_rejects_non_percentages() {
            assert!((parse_decided_percent("80").unwrap() - 80.0).abs() < f64::EPSILON);
            for invalid in ["-0.1", "100.1", "NaN", "inf", "not-a-number"] {
                assert!(
                    parse_decided_percent(invalid).is_err(),
                    "invalid decided-rate threshold must be rejected: {invalid}"
                );
            }
        }

        #[test]
        fn corpus_manifest_validates_membership_hashes_and_named_tier() {
            let bytes = serde_json::to_vec(&micro_manifest_value()).unwrap();
            let selection = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("micro-manifest.json"),
                &bytes,
                Some("representative"),
            )
            .unwrap();
            assert_eq!(selection.total_entries, 3);
            assert_eq!(selection.entries.len(), 2);
            assert_eq!(selection.entries[0].path, "sat-add.smt2");
            assert_eq!(selection.entries[1].path, "unsat-ult-zero.smt2");
            assert_eq!(selection.selected_tier.as_deref(), Some("representative"));
            assert_eq!(selection.manifest_hash, content_hash(&bytes));
        }

        #[test]
        fn capture_index_generates_deterministic_self_validating_manifest() {
            let index = serde_json::to_vec(&micro_capture_index_value()).unwrap();
            let first = render_corpus_manifest_from_capture_index(
                &micro_corpus_root(),
                Path::new("capture-index.json"),
                &index,
                Path::new("generated-manifest.json"),
            )
            .unwrap();
            let second = render_corpus_manifest_from_capture_index(
                &micro_corpus_root(),
                Path::new("capture-index.json"),
                &index,
                Path::new("generated-manifest.json"),
            )
            .unwrap();
            assert_eq!(first, second);
            assert_eq!(first.last(), Some(&b'\n'));

            let selection = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("generated-manifest.json"),
                &first,
                Some("representative"),
            )
            .unwrap();
            assert_eq!(selection.total_entries, 3);
            assert_eq!(selection.entries.len(), 2);
            assert_eq!(
                selection.entries[0].content_hash,
                content_hash(&fs::read(micro_corpus_root().join("sat-add.smt2")).unwrap())
            );
        }

        #[test]
        fn capture_index_rejects_stale_hashes_and_incomplete_membership() {
            let mut stale_hash = micro_capture_index_value();
            stale_hash["files"][0]["content_hash"] =
                json!("sha256:0000000000000000000000000000000000000000000000000000000000000000");
            let error = render_corpus_manifest_from_capture_index(
                &micro_corpus_root(),
                Path::new("capture-index.json"),
                &serde_json::to_vec(&stale_hash).unwrap(),
                Path::new("generated-manifest.json"),
            )
            .unwrap_err();
            assert!(error.contains("unknown field `content_hash`"), "{error}");

            let mut incomplete = micro_capture_index_value();
            incomplete["files"].as_array_mut().unwrap().pop();
            let error = render_corpus_manifest_from_capture_index(
                &micro_corpus_root(),
                Path::new("capture-index.json"),
                &serde_json::to_vec(&incomplete).unwrap(),
                Path::new("generated-manifest.json"),
            )
            .unwrap_err();
            assert!(
                error.contains("capture index membership mismatch"),
                "{error}"
            );
            assert!(error.contains("unsat-ult-zero.smt2"), "{error}");
        }

        #[test]
        fn corpus_manifest_rejects_content_drift_and_unlisted_queries() {
            let mut drifted = micro_manifest_value();
            drifted["files"][0]["content_hash"] =
                json!("sha256:0000000000000000000000000000000000000000000000000000000000000000");
            let error = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("micro-manifest.json"),
                &serde_json::to_vec(&drifted).unwrap(),
                None,
            )
            .unwrap_err();
            assert!(error.contains("hash mismatch"), "{error}");

            let mut incomplete = micro_manifest_value();
            incomplete["files"].as_array_mut().unwrap().pop();
            let error = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("micro-manifest.json"),
                &serde_json::to_vec(&incomplete).unwrap(),
                None,
            )
            .unwrap_err();
            assert!(error.contains("membership mismatch"), "{error}");
            assert!(error.contains("unsat-ult-zero.smt2"), "{error}");
        }

        #[test]
        fn corpus_manifest_rejects_unsafe_duplicates_and_empty_tiers() {
            let mut unsafe_path = micro_manifest_value();
            unsafe_path["files"][0]["path"] = json!("../sat-add.smt2");
            let error = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("micro-manifest.json"),
                &serde_json::to_vec(&unsafe_path).unwrap(),
                None,
            )
            .unwrap_err();
            assert!(error.contains("normalized relative"), "{error}");

            let mut duplicate = micro_manifest_value();
            duplicate["files"][1]["path"] = duplicate["files"][0]["path"].clone();
            duplicate["files"][1]["content_hash"] = duplicate["files"][0]["content_hash"].clone();
            let error = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("micro-manifest.json"),
                &serde_json::to_vec(&duplicate).unwrap(),
                None,
            )
            .unwrap_err();
            assert!(error.contains("duplicate corpus manifest path"), "{error}");

            let error = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("micro-manifest.json"),
                &serde_json::to_vec(&micro_manifest_value()).unwrap(),
                Some("nightly"),
            )
            .unwrap_err();
            assert!(error.contains("selects no files"), "{error}");
        }

        #[test]
        fn corpus_manifest_expected_verdict_is_an_independent_integrity_gate() {
            let entry = CorpusManifestEntry {
                path: "query.smt2".to_owned(),
                content_hash:
                    "sha256:0000000000000000000000000000000000000000000000000000000000000000"
                        .to_owned(),
                expected: "unsat".to_owned(),
                family: "comparison".to_owned(),
                tiers: vec!["representative".to_owned()],
            };
            let mut record = json!({"outcome": "sat"});
            let mut summary = Summary {
                files: 1,
                sat: 1,
                ..Summary::default()
            };
            annotate_manifest_result(&mut record, &entry, &mut summary);
            assert_eq!(summary.manifest_expected, 1);
            assert_eq!(summary.manifest_compared, 1);
            assert_eq!(summary.manifest_disagree, 1);
            assert_eq!(
                record["corpus_manifest"]["decision_agrees"],
                JsonValue::Bool(false)
            );
            assert_eq!(
                report_summary(&summary, Some(100.0), false),
                ExitCode::FAILURE
            );
        }

        #[test]
        fn layer_attribution_reports_cold_stages_and_exact_percentiles() {
            let samples = vec![
                LayerSample {
                    word_preprocess: 0.001,
                    bit_blast: 0.002,
                    cnf_encode: 0.003,
                    cnf_inprocess: 0.004,
                    solve: 0.005,
                    model_lift: 0.001,
                    model_replay: 0.0005,
                    aig_inputs: 8,
                    aig_nodes: 16,
                    cnf_variables: 24,
                    cnf_clauses: 32,
                },
                LayerSample {
                    word_preprocess: 0.010,
                    bit_blast: 0.020,
                    cnf_encode: 0.030,
                    cnf_inprocess: 0.040,
                    solve: 0.050,
                    model_lift: 0.010,
                    model_replay: 0.005,
                    aig_inputs: 80,
                    aig_nodes: 160,
                    cnf_variables: 240,
                    cnf_clauses: 320,
                },
            ];
            let summary = Summary {
                layer_files: 2,
                layer_word_preprocess_s: 0.011,
                layer_bit_blast_s: 0.022,
                layer_cnf_encode_s: 0.033,
                layer_cnf_inprocess_s: 0.044,
                layer_solve_s: 0.055,
                layer_model_lift_s: 0.011,
                layer_model_replay_s: 0.0055,
                layer_model_replay_files: 1,
                layer_samples: samples,
                ..Summary::default()
            };
            let record = layer_attribution_record(&summary);
            assert!((record["total_pipeline_s"].as_f64().unwrap() - 0.1815).abs() < f64::EPSILON);
            assert_eq!(
                record["distributions"]["word_preprocess"]["p50_ms"],
                json!(1.0)
            );
            assert_eq!(
                record["distributions"]["word_preprocess"]["p95_ms"],
                json!(10.0)
            );
            assert_eq!(record["distributions"]["total"]["p50_ms"], json!(16.5));
            assert!(
                (record["distributions"]["total"]["p95_ms"].as_f64().unwrap() - 165.0).abs() < 1e-9
            );
            assert_eq!(
                record["distributions"]["model_replay"]["p50_ms"],
                json!(0.5)
            );
            assert_eq!(record["model_replay_instances"], json!(1));
            assert_eq!(record["sat_dominates"], json!(false));
            assert_eq!(record["size_distributions"]["aig_nodes"]["p50"], json!(16));
            assert_eq!(
                record["size_distributions"]["cnf_clauses"]["p95"],
                json!(320)
            );
        }

        #[test]
        fn requested_unsat_proof_replay_is_an_independent_gate() {
            let mut record = SolveRecord {
                outcome: "unsat",
                detail: None,
                stats: SolveStats::default(),
                model_replay: Duration::ZERO,
                model_replay_failure: false,
            };
            assert_eq!(proof_replay_status(&record, false), "not-requested");
            assert_eq!(proof_replay_status(&record, true), "missing");

            let mut missing = Summary::default();
            accumulate_proof_replay(&record, true, &mut missing);
            assert_eq!(missing.unsat_proof_replay_missing, 1);
            assert_eq!(report_summary(&missing, None, false), ExitCode::FAILURE);

            record
                .stats
                .backend
                .push(("unsat_proof_checked_inline".to_owned(), 1.0));
            record
                .stats
                .backend
                .push(("unsat_proof_replay_ms".to_owned(), 0.25));
            assert_eq!(proof_replay_status(&record, true), "checked");
            let mut checked = Summary::default();
            accumulate_proof_replay(&record, true, &mut checked);
            assert_eq!(checked.unsat_proof_replay_checked, 1);
            assert_eq!(checked.unsat_proof_replay_missing, 0);
            assert_eq!(checked.unsat_proof_replay_sample, Some(0.00025));
        }

        #[test]
        fn determinism_profile_reports_the_options_backends_actually_consume() {
            let record = determinism_record();
            assert_eq!(record["profile"], json!(DETERMINISM_PROFILE));
            assert_eq!(record["sat_bv"]["random_seed"], json!(91_648_253.0));
            assert_eq!(record["sat_bv"]["random_var_freq"], json!(0.0));
            assert_eq!(record["sat_bv"]["random_polarity"], json!(false));
            assert_eq!(record["sat_bv"]["random_initial_activity"], json!(false));
            #[cfg(feature = "z3")]
            {
                assert_eq!(
                    record["z3"]["random_seed"],
                    json!(DETERMINISTIC_Z3_RANDOM_SEED)
                );
                assert_eq!(record["z3"]["set_explicitly"], json!(true));
            }
            #[cfg(not(feature = "z3"))]
            assert!(record["z3"].is_null());
        }

        #[test]
        fn deterministic_resource_gate_requires_every_positive_limit() {
            assert!(
                missing_deterministic_resource_limits(
                    Some(2_000_000),
                    Some(300_000),
                    Some(3_000_000),
                    Some(8_000_000),
                )
                .is_empty()
            );
            assert_eq!(
                missing_deterministic_resource_limits(Some(0), None, Some(1), Some(0)),
                vec!["--resource-limit", "--node-budget", "--cnf-clause-budget"]
            );
        }

        fn complete_experiment_identity() -> ExperimentIdentity {
            let mut identity = ExperimentIdentity {
                source_revision: Some("0123456789abcdef".to_owned()),
                source_dirty: Some(false),
                cargo_lock_hash: Some("sha256:lock".to_owned()),
                rustc: Some("rustc 1.88.0\nhost: x86_64-unknown-linux-gnu".to_owned()),
                cargo: Some("cargo 1.88.0".to_owned()),
                build_profile: "release".to_owned(),
                backend: "axeyum-sat-bv rustsat-batsat".to_owned(),
                compare_backend: Some("z3 4.13.3.0".to_owned()),
                hardware: HardwareIdentity {
                    os: "linux".to_owned(),
                    arch: "x86_64".to_owned(),
                    parallelism: 16,
                    cpu_model: Some("Test CPU".to_owned()),
                    kernel: Some("Linux 6.8 x86_64 GNU/Linux".to_owned()),
                    total_memory_bytes: Some(64 * 1024 * 1024 * 1024),
                },
                environment_hash: String::new(),
            };
            identity.environment_hash = identity.compute_environment_hash();
            identity
        }

        #[test]
        fn reproducible_run_identity_is_complete_and_source_revision_is_not_environment() {
            let identity = complete_experiment_identity();
            assert_eq!(identity.require_reproducible(), Ok(()));

            let mut next_commit = identity.clone();
            next_commit.source_revision = Some("fedcba9876543210".to_owned());
            assert_eq!(
                next_commit.compute_environment_hash(),
                identity.environment_hash,
                "per-commit comparison keeps the environment key stable"
            );

            let mut dirty = identity.clone();
            dirty.source_dirty = Some(true);
            let error = dirty.require_reproducible().unwrap_err();
            assert!(error.contains("clean source tree"), "{error}");

            let mut changed_cpu = identity.clone();
            changed_cpu.hardware.cpu_model = Some("Different CPU".to_owned());
            assert_ne!(
                changed_cpu.compute_environment_hash(),
                identity.environment_hash
            );
        }

        #[test]
        fn linux_hardware_identity_parsers_are_strict() {
            assert_eq!(
                parse_cpu_model("processor : 0\nmodel name : Axeyum Test CPU\n"),
                Some("Axeyum Test CPU".to_owned())
            );
            assert_eq!(
                parse_cpu_model("Processor : Cortex-A76\n"),
                Some("Cortex-A76".to_owned())
            );
            assert_eq!(parse_cpu_model("processor : 0\n"), None);
            assert_eq!(
                parse_total_memory_bytes("MemTotal:       65536 kB\nMemFree: 1 kB\n"),
                Some(67_108_864)
            );
            assert_eq!(parse_total_memory_bytes("MemTotal: 1 MB\n"), None);
        }

        #[test]
        fn query_shape_profiles_lifter_ops_and_rewrite_opportunities() {
            let text = "\
                (set-logic QF_ABV)\n\
                (declare-const x (_ BitVec 8))\n\
                (declare-const y (_ BitVec 8))\n\
                (declare-const a (Array (_ BitVec 8) (_ BitVec 16)))\n\
                (assert (= ((_ extract 7 0) ((_ zero_extend 8) x)) x))\n\
                (assert (= ((_ extract 6 1) ((_ extract 7 0) ((_ sign_extend 8) y)))\n\
                           ((_ extract 6 1) y)))\n\
                (assert (= ((_ extract 11 4) (concat x y))\n\
                           ((_ extract 11 4) (concat x y))))\n\
                (assert (= (select (store a x ((_ zero_extend 8) y)) x)\n\
                           ((_ zero_extend 8) y)))\n\
                (check-sat)\n";
            let script = parse_script(text).expect("shape fixture parses");
            let stats = TermStats::compute(&script.arena, &script.assertions);
            let shape = QueryShapeSample::compute(&script.arena, &script.assertions, &stats);
            assert_eq!(shape.extract_over_concat, 1);
            assert_eq!(shape.extract_over_extract, 1);
            assert_eq!(shape.extract_over_zero_ext, 1);
            assert_eq!(shape.extract_over_sign_ext, 1);
            assert_eq!(shape.low_extract_over_zero_ext, 1);
            assert_eq!(shape.cancellation_opportunities(), 4);
            assert_eq!((shape.selects, shape.stores), (1, 1));
            assert!(shape.distinct_bitvec_widths >= 3);

            let summary = Summary {
                query_shape_files: 1,
                query_shape_samples: vec![shape],
                ..Summary::default()
            };
            let record = query_shape_summary_record(&summary);
            assert_eq!(
                record["coercion_cancellation_opportunities"]["total"],
                json!(4)
            );
            assert_eq!(
                record["memory_provenance"]["surviving_select_store_ops"],
                json!(2)
            );
            assert_eq!(
                record["formula_distributions"]["dag_nodes"]["p50"],
                json!(shape.dag_nodes)
            );
        }

        #[test]
        fn client_comparison_uses_aggregate_ratio_and_distributions() {
            let summary = Summary {
                client_comparison_files: 2,
                client_axeyum_s: 0.040,
                client_z3_s: 0.020,
                client_comparison_samples: vec![
                    ClientComparisonSample {
                        axeyum_s: 0.010,
                        z3_s: 0.005,
                    },
                    ClientComparisonSample {
                        axeyum_s: 0.030,
                        z3_s: 0.015,
                    },
                ],
                ..Summary::default()
            };
            let record = client_comparison_record(&summary);
            assert_eq!(record["axeyum_over_z3_ratio"], json!(2.0));
            assert_eq!(record["axeyum"]["p50_ms"], json!(10.0));
            assert_eq!(record["axeyum"]["p95_ms"], json!(30.0));
            assert_eq!(record["z3"]["p50_ms"], json!(5.0));
            assert_eq!(record["z3"]["p95_ms"], json!(15.0));
        }

        #[test]
        fn corpus_merge_retains_one_profile_sample_per_instance() {
            let layer = LayerSample {
                word_preprocess: 0.001,
                bit_blast: 0.002,
                cnf_encode: 0.003,
                cnf_inprocess: 0.0,
                solve: 0.004,
                model_lift: 0.001,
                model_replay: 0.0005,
                aig_inputs: 8,
                aig_nodes: 16,
                cnf_variables: 24,
                cnf_clauses: 32,
            };
            let comparison = ClientComparisonSample {
                axeyum_s: 0.011,
                z3_s: 0.007,
            };
            let next = Summary {
                layer_files: 1,
                layer_sample: Some(layer),
                query_shape_files: 1,
                query_shape_sample: Some(QueryShapeSample {
                    dag_nodes: 42,
                    ..QueryShapeSample::default()
                }),
                client_comparison_files: 1,
                client_comparison_sample: Some(comparison),
                ..Summary::default()
            };
            let mut total = Summary::default();
            merge_summary(&mut total, &next);
            assert_eq!(total.layer_samples.len(), 1);
            assert_eq!(total.query_shape_samples.len(), 1);
            assert_eq!(total.query_shape_samples[0].dag_nodes, 42);
            assert_eq!(total.client_comparison_samples.len(), 1);
            assert!((total.layer_samples[0].total_s() - layer.total_s()).abs() < f64::EPSILON);
            assert!(
                (total.client_comparison_samples[0].z3_s - comparison.z3_s).abs() < f64::EPSILON
            );
        }

        #[test]
        fn under_parse_guard_flags_check_sat_assuming_with_assumptions() {
            // A `check-sat-assuming` with an inline assumption: the flat assertion
            // view omits it, so the harness must NOT report a real verdict.
            let text = "\
                (set-logic QF_UF)\n\
                (declare-const p Bool)\n\
                (assert (or p (not p)))\n\
                (check-sat-assuming (p))\n";
            let script = parse_script(text).expect("parses");
            let reason = under_parsed_reason(&script, text);
            assert!(
                reason.is_some_and(|r| r.contains("check-sat-assuming")),
                "inline-assumption check-sat-assuming must be flagged unsupported",
            );
        }

        #[test]
        fn under_parse_guard_allows_plain_check_sat_assuming_empty() {
            // An *empty* assumption list is equivalent to `check-sat`; not flagged.
            let text = "\
                (set-logic QF_UF)\n\
                (declare-const p Bool)\n\
                (assert p)\n\
                (check-sat-assuming ())\n";
            let script = parse_script(text).expect("parses");
            assert!(
                under_parsed_reason(&script, text).is_none(),
                "empty check-sat-assuming is faithful and must not be flagged",
            );
        }

        #[test]
        fn under_parse_guard_flags_zero_assertions_from_constraint_text() {
            // If the flat view is empty but the source plainly carries an assert,
            // constraints were dropped — solving "nothing" is a vacuous verdict.
            let text = "(assert true)";
            // Build a Script that parsed no assertions but whose source has `assert`.
            let mut script = Script::default();
            script.assertions.clear();
            assert!(
                under_parsed_reason(&script, text).is_some(),
                "0 parsed assertions over constraint-bearing text must be flagged",
            );
        }

        #[test]
        fn under_parse_guard_allows_genuinely_empty_benchmark() {
            // A truly empty benchmark (no constraints) is faithfully empty.
            let text = "(set-logic QF_UF)\n(check-sat)\n";
            let script = parse_script(text).expect("parses");
            assert!(
                under_parsed_reason(&script, text).is_none(),
                "a constraint-free benchmark must not be flagged",
            );
        }

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
