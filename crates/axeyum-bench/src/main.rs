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
//!   `[--rewrite off|default] [--backend sat-bv|incremental-bv-batch|incremental-bv-raw-profile|z3]`
//!   `[--query-plan full|first-assertion-support|replay-refine|replay-refine-exact]`
//!   `[--refine-rounds N] [--refine-batch N] [--refine-adaptive-batch]`
//!   `[--refine-select first|smallest-dag|smallest-plan-dag|smallest-plan-greedy]`
//!   `[--resource-limit N] [--node-budget N] [--cnf-var-budget N]`
//!   `[--cnf-clause-budget N] [--require-deterministic-resources]`
//!   `[--prove-unsat]`
//!   `[--certify-end-to-end-unsat --end-to-end-deadline-ms N]`
//!   `[--end-to-end-process-timeout-ms N]`
//!   `[--require-reproducible-run]`
//!   `[--compare-z3] [--require-in-process-z3] [--min-decided-percent P]`
//!   `[--jobs N] [--manifest-jobs N]`
//! The default build can run the pure Rust `sat-bv` backend. Build with
//! `--features z3` (or `z3-static`) to enable the Z3 oracle backend.

mod certificate_process;

fn main() -> std::process::ExitCode {
    if let Some(exit) = certificate_process::maybe_worker_main() {
        return exit;
    }
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
        Canonicalizer, DEFAULT_SOLVE_EQS_FUEL, ModelReconstructionTrail, RewriteManifest,
        RewriteReport, canonicalize_terms, default_manifest, propagate_values, solve_eqs_bounded,
    };
    use axeyum_smtlib::{Script, ScriptCommand, SmtError, parse_script};
    use axeyum_solver::{
        BvLayerStats, Capabilities, CheckResult, EndToEndUnsatOutcome, IncrementalBvSolver,
        IncrementalBvStats, LazyBvBackend, Model, RangeDemandDecision, RangeDemandPolicy,
        SatBvBackend, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
        certify_qf_bv_unsat_end_to_end_within, check_model_with_assignment, solve,
    };
    #[cfg(feature = "z3")]
    use axeyum_solver::{DETERMINISTIC_Z3_RANDOM_SEED, Z3Backend};
    use rayon::prelude::*;
    use serde_json::{Value as JsonValue, json};
    use sha2::{Digest, Sha256};

    use crate::certificate_process::{IsolatedStatus, certify_file_isolated};

    const ARTIFACT_VERSION: u32 = 34;
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
        /// A fresh [`IncrementalBvSolver`] per query with all roots admitted by
        /// one shared-memo canonical batch, matching Glaurung's cold embedding.
        IncrementalBvBatch,
        /// Attribution-only fresh raw incremental path. It enables the opt-in
        /// phase/gate counters and therefore is not a performance baseline.
        IncrementalBvRawProfile,
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
                BackendKind::IncrementalBvBatch => "incremental-bv-batch",
                BackendKind::IncrementalBvRawProfile => "incremental-bv-raw-profile",
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
        rewrite_disabled_rules: Vec<String>,
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
        certify_end_to_end_unsat: bool,
        end_to_end_deadline_ms: Option<u64>,
        end_to_end_process_timeout_ms: Option<u64>,
        preprocess: bool,
        profile_bit_demand: bool,
        demand_bit_slicing: bool,
        range_demand_slicing: bool,
        range_demand_policy: RangeDemandPolicy,
        compare_z3: bool,
        require_in_process_z3: bool,
        require_reproducible_run: bool,
        require_deterministic_resources: bool,
        min_decided_percent: Option<f64>,
        jobs: usize,
        manifest_jobs: usize,
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
            rewrite_disabled_rules: Vec::new(),
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
            certify_end_to_end_unsat: false,
            end_to_end_deadline_ms: None,
            end_to_end_process_timeout_ms: None,
            preprocess: false,
            profile_bit_demand: false,
            demand_bit_slicing: false,
            range_demand_slicing: false,
            range_demand_policy: RangeDemandPolicy::default(),
            compare_z3: false,
            require_in_process_z3: false,
            require_reproducible_run: false,
            require_deterministic_resources: false,
            min_decided_percent: None,
            jobs: 1,
            manifest_jobs: 1,
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
            "--rewrite-disable-rule" => {
                parsed.rewrite_disabled_rules.push(next_value(args, flag)?);
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
            "--certify-end-to-end-unsat" => parsed.certify_end_to_end_unsat = true,
            "--end-to-end-deadline-ms" => {
                parsed.end_to_end_deadline_ms = Some(
                    next_value(args, flag)?
                        .parse()
                        .map_err(|e| format!("{e}"))?,
                );
            }
            "--end-to-end-process-timeout-ms" => {
                parsed.end_to_end_process_timeout_ms = Some(
                    next_value(args, flag)?
                        .parse()
                        .map_err(|e| format!("{e}"))?,
                );
            }
            "--preprocess" => parsed.preprocess = true,
            "--profile-bit-demand" => parsed.profile_bit_demand = true,
            "--demand-bit-slicing" => parsed.demand_bit_slicing = true,
            "--range-demand-slicing" => parsed.range_demand_slicing = true,
            "--range-demand-min-term-bits" => {
                parsed.range_demand_policy.min_term_bits_available = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
            "--range-demand-min-estimated-bits" => {
                parsed.range_demand_policy.min_estimated_bits_avoided = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
            "--range-demand-min-estimated-percent" => {
                parsed.range_demand_policy.min_estimated_avoided_percent = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
            "--range-demand-min-exact-bits" => {
                parsed.range_demand_policy.min_exact_bits_avoided = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
            "--range-demand-min-exact-percent" => {
                parsed.range_demand_policy.min_exact_avoided_percent = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
            "--range-demand-work-budget" => {
                parsed.range_demand_policy.analysis_work_budget = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
            }
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
            "--manifest-jobs" => {
                parsed.manifest_jobs = next_value(args, flag)?
                    .parse()
                    .map_err(|e| format!("{e}"))?;
                if parsed.manifest_jobs == 0 {
                    return Err("`--manifest-jobs` must be at least 1".to_owned());
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
        validate_rewrite_ablation(args)?;
        if args.require_in_process_z3 && !args.compare_z3 {
            return Err("`--require-in-process-z3` requires `--compare-z3`".to_owned());
        }
        if args.prove_unsat && !matches!(args.backend, BackendKind::SatBv) {
            return Err("`--prove-unsat` requires `--backend sat-bv`".to_owned());
        }
        validate_end_to_end_certification(args)?;
        if args.profile_bit_demand && !matches!(args.backend, BackendKind::SatBv) {
            return Err("`--profile-bit-demand` requires `--backend sat-bv`".to_owned());
        }
        if args.demand_bit_slicing && !matches!(args.backend, BackendKind::SatBv) {
            return Err("`--demand-bit-slicing` requires `--backend sat-bv`".to_owned());
        }
        if args.range_demand_slicing && !matches!(args.backend, BackendKind::SatBv) {
            return Err("`--range-demand-slicing` requires `--backend sat-bv`".to_owned());
        }
        if args.range_demand_slicing && args.demand_bit_slicing {
            return Err(
                "`--range-demand-slicing` and `--demand-bit-slicing` are distinct experiments and cannot be combined"
                    .to_owned(),
            );
        }
        if !args.range_demand_slicing && args.range_demand_policy != RangeDemandPolicy::default() {
            return Err("range-demand threshold flags require `--range-demand-slicing`".to_owned());
        }
        if args.range_demand_policy.min_estimated_avoided_percent > 100
            || args.range_demand_policy.min_exact_avoided_percent > 100
        {
            return Err("range-demand percentages must be between 0 and 100".to_owned());
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

    fn validate_end_to_end_certification(args: &Args) -> Result<(), String> {
        if !args.certify_end_to_end_unsat {
            if args.end_to_end_deadline_ms.is_some() || args.end_to_end_process_timeout_ms.is_some()
            {
                return Err("end-to-end deadline/isolation flags require \
                     `--certify-end-to-end-unsat`"
                    .to_owned());
            }
            return Ok(());
        }
        let deadline_ms = args
            .end_to_end_deadline_ms
            .ok_or("`--certify-end-to-end-unsat` requires `--end-to-end-deadline-ms`")?;
        if !(1..=600_000).contains(&deadline_ms) {
            return Err("`--end-to-end-deadline-ms` must be in 1..=600000".to_owned());
        }
        if let Some(process_timeout_ms) = args.end_to_end_process_timeout_ms
            && !(1..=600_000).contains(&process_timeout_ms)
        {
            return Err("`--end-to-end-process-timeout-ms` must be in 1..=600000".to_owned());
        }
        if !matches!(args.backend, BackendKind::SatBv) {
            return Err("`--certify-end-to-end-unsat` requires `--backend sat-bv`".to_owned());
        }
        if !args.prove_unsat {
            return Err("`--certify-end-to-end-unsat` requires `--prove-unsat`".to_owned());
        }
        if args.rewrite != RewriteMode::Off
            || args.query_plan != QueryPlanMode::Full
            || args.preprocess
            || args.demand_bit_slicing
            || args.range_demand_slicing
            || args.cnf_inprocessing
            || args.cnf_vivify
            || args.native_cdcl
        {
            return Err(
                "`--certify-end-to-end-unsat` requires the raw full-query path: \
                 `--rewrite off`, `--query-plan full`, and no preprocessing, demand slicing, \
                 CNF inprocessing/vivification, or native-CDCL override"
                    .to_owned(),
            );
        }
        Ok(())
    }

    fn validate_rewrite_ablation(args: &Args) -> Result<(), String> {
        if args.rewrite_disabled_rules.is_empty() {
            return Ok(());
        }
        if args.rewrite != RewriteMode::Default {
            return Err("`--rewrite-disable-rule` requires `--rewrite default`".to_owned());
        }
        let enabled = default_manifest()
            .enabled_rules()
            .map(|rule| rule.id.as_str().to_owned())
            .collect::<BTreeSet<_>>();
        let mut seen = BTreeSet::new();
        for rule_id in &args.rewrite_disabled_rules {
            if !seen.insert(rule_id) {
                return Err(format!(
                    "rewrite ablation repeats disabled rule `{rule_id}`"
                ));
            }
            if !enabled.contains(rule_id) {
                return Err(format!(
                    "rewrite ablation names unknown or non-default rule `{rule_id}`"
                ));
            }
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
            "incremental-bv-batch" => Ok(BackendKind::IncrementalBvBatch),
            "incremental-bv-raw-profile" => Ok(BackendKind::IncrementalBvRawProfile),
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

    #[derive(Debug, Clone, Copy, Default)]
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
        aig_and_requests: u64,
        aig_and_trivial_simplifications: u64,
        aig_and_absorption_simplifications: u64,
        aig_and_structural_hash_hits: u64,
        aig_and_nodes_created: u64,
        bit_demand_analysis: f64,
        bit_demand_profile_complete: bool,
        bit_demand_lowering_applied: bool,
        range_demand_decision: RangeDemandDecision,
        range_demand_admission: f64,
        range_demand_estimated_bits_avoided: u64,
        range_demand_analysis_work_budget: u64,
        range_demand_analysis_work: u64,
        range_demand_merges: u64,
        range_demand_promotions: u64,
        term_bit_requests: u64,
        term_bits_available: u64,
        term_bits_demanded: u64,
        term_bits_lowered: u64,
        symbol_bit_requests: u64,
        symbol_bits_available: u64,
        symbol_bits_demanded: u64,
        symbol_bits_lowered: u64,
        cnf_variables: u64,
        cnf_clauses: u64,
        cnf_planning: f64,
        cnf_variable_allocation: f64,
        cnf_gate_encoding: f64,
        cnf_root_encoding: f64,
        cnf_reachable_nodes: u64,
        cnf_skipped_helper_nodes: u64,
        cnf_direct_root_nodes: u64,
        cnf_xor_gates: u64,
        cnf_not_ite_gates: u64,
        cnf_not_and_gates: u64,
        cnf_and_tree_gates: u64,
        cnf_binary_and_gates: u64,
        cnf_clause_attempts: u64,
        cnf_tautological_clauses_skipped: u64,
        cnf_duplicate_clauses_skipped: u64,
    }

    /// Original-query structural profile used to verify that an external `QF_BV`
    /// tier actually has the binary-lifter shape it claims to represent. Counts
    /// are over unique reachable DAG nodes, so parser-preserved sharing cannot
    /// inflate an operator family by repeated tree expansion.
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    struct QfBvOperatorCounts {
        bool_not: u64,
        bool_and: u64,
        bool_or: u64,
        bool_xor: u64,
        bool_implies: u64,
        bv_not: u64,
        bv_and: u64,
        bv_or: u64,
        bv_xor: u64,
        bv_nand: u64,
        bv_nor: u64,
        bv_xnor: u64,
        bv_neg: u64,
        bv_add: u64,
        bv_sub: u64,
        bv_mul: u64,
        bv_udiv: u64,
        bv_urem: u64,
        bv_sdiv: u64,
        bv_srem: u64,
        bv_smod: u64,
        bv_shl: u64,
        bv_lshr: u64,
        bv_ashr: u64,
        bv_ult: u64,
        bv_ule: u64,
        bv_ugt: u64,
        bv_uge: u64,
        bv_slt: u64,
        bv_sle: u64,
        bv_sgt: u64,
        bv_sge: u64,
        eq: u64,
        ite: u64,
        bv_comp: u64,
        extract: u64,
        concat: u64,
        zero_extend: u64,
        sign_extend: u64,
        rotate_left: u64,
        rotate_right: u64,
        other: u64,
    }

    impl QfBvOperatorCounts {
        fn record(&mut self, op: Op) {
            let counter = match op {
                Op::BoolNot => &mut self.bool_not,
                Op::BoolAnd => &mut self.bool_and,
                Op::BoolOr => &mut self.bool_or,
                Op::BoolXor => &mut self.bool_xor,
                Op::BoolImplies => &mut self.bool_implies,
                Op::BvNot => &mut self.bv_not,
                Op::BvAnd => &mut self.bv_and,
                Op::BvOr => &mut self.bv_or,
                Op::BvXor => &mut self.bv_xor,
                Op::BvNand => &mut self.bv_nand,
                Op::BvNor => &mut self.bv_nor,
                Op::BvXnor => &mut self.bv_xnor,
                Op::BvNeg => &mut self.bv_neg,
                Op::BvAdd => &mut self.bv_add,
                Op::BvSub => &mut self.bv_sub,
                Op::BvMul => &mut self.bv_mul,
                Op::BvUdiv => &mut self.bv_udiv,
                Op::BvUrem => &mut self.bv_urem,
                Op::BvSdiv => &mut self.bv_sdiv,
                Op::BvSrem => &mut self.bv_srem,
                Op::BvSmod => &mut self.bv_smod,
                Op::BvShl => &mut self.bv_shl,
                Op::BvLshr => &mut self.bv_lshr,
                Op::BvAshr => &mut self.bv_ashr,
                Op::BvUlt => &mut self.bv_ult,
                Op::BvUle => &mut self.bv_ule,
                Op::BvUgt => &mut self.bv_ugt,
                Op::BvUge => &mut self.bv_uge,
                Op::BvSlt => &mut self.bv_slt,
                Op::BvSle => &mut self.bv_sle,
                Op::BvSgt => &mut self.bv_sgt,
                Op::BvSge => &mut self.bv_sge,
                Op::Eq => &mut self.eq,
                Op::Ite => &mut self.ite,
                Op::BvComp => &mut self.bv_comp,
                Op::Extract { .. } => &mut self.extract,
                Op::Concat => &mut self.concat,
                Op::ZeroExt { .. } => &mut self.zero_extend,
                Op::SignExt { .. } => &mut self.sign_extend,
                Op::RotateLeft { .. } => &mut self.rotate_left,
                Op::RotateRight { .. } => &mut self.rotate_right,
                _ => &mut self.other,
            };
            *counter = counter.saturating_add(1);
        }

        fn applications(&self) -> u64 {
            [
                self.bool_not,
                self.bool_and,
                self.bool_or,
                self.bool_xor,
                self.bool_implies,
                self.bv_not,
                self.bv_and,
                self.bv_or,
                self.bv_xor,
                self.bv_nand,
                self.bv_nor,
                self.bv_xnor,
                self.bv_neg,
                self.bv_add,
                self.bv_sub,
                self.bv_mul,
                self.bv_udiv,
                self.bv_urem,
                self.bv_sdiv,
                self.bv_srem,
                self.bv_smod,
                self.bv_shl,
                self.bv_lshr,
                self.bv_ashr,
                self.bv_ult,
                self.bv_ule,
                self.bv_ugt,
                self.bv_uge,
                self.bv_slt,
                self.bv_sle,
                self.bv_sgt,
                self.bv_sge,
                self.eq,
                self.ite,
                self.bv_comp,
                self.extract,
                self.concat,
                self.zero_extend,
                self.sign_extend,
                self.rotate_left,
                self.rotate_right,
                self.other,
            ]
            .into_iter()
            .fold(0, u64::saturating_add)
        }

        fn merge(&mut self, other: Self) {
            macro_rules! merge_fields {
                ($($field:ident),+ $(,)?) => {
                    $(self.$field = self.$field.saturating_add(other.$field);)+
                };
            }
            merge_fields!(
                bool_not,
                bool_and,
                bool_or,
                bool_xor,
                bool_implies,
                bv_not,
                bv_and,
                bv_or,
                bv_xor,
                bv_nand,
                bv_nor,
                bv_xnor,
                bv_neg,
                bv_add,
                bv_sub,
                bv_mul,
                bv_udiv,
                bv_urem,
                bv_sdiv,
                bv_srem,
                bv_smod,
                bv_shl,
                bv_lshr,
                bv_ashr,
                bv_ult,
                bv_ule,
                bv_ugt,
                bv_uge,
                bv_slt,
                bv_sle,
                bv_sgt,
                bv_sge,
                eq,
                ite,
                bv_comp,
                extract,
                concat,
                zero_extend,
                sign_extend,
                rotate_left,
                rotate_right,
                other,
            );
        }
    }

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
        low_extract_over_sign_ext: u64,
        extract_concat_low_side: u64,
        extract_concat_high_side: u64,
        extract_concat_straddling: u64,
        extract_concat_whole_low: u64,
        extract_concat_whole_high: u64,
        extract_zero_ext_low_region: u64,
        extract_zero_ext_high_region: u64,
        extract_zero_ext_straddling: u64,
        extract_sign_ext_low_region: u64,
        extract_sign_ext_high_region: u64,
        extract_sign_ext_straddling: u64,
        max_nested_extract_depth: u64,
        qfbv_operators: QfBvOperatorCounts,
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
                sample.qfbv_operators.record(*op);
                match *op {
                    Op::Extract { hi, lo } => sample.record_extract(arena, args[0], hi, lo),
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

        fn record_extract(&mut self, arena: &TermArena, source: TermId, hi: u32, lo: u32) {
            self.extracts += 1;
            let result_width = hi - lo + 1;
            self.extract_result_bits += u64::from(result_width);
            let source_width = arena.sort_of(source).bv_width().unwrap_or(0);
            self.extract_source_bits += u64::from(source_width);
            self.narrow_extracts += u64::from(result_width < source_width);
            let TermNode::App {
                op: child_op,
                args: child_args,
            } = arena.node(source)
            else {
                return;
            };
            match child_op {
                Op::Concat => {
                    self.extract_over_concat += 1;
                    let low_width = arena.sort_of(child_args[1]).bv_width().unwrap_or(0);
                    if hi < low_width {
                        self.extract_concat_low_side += 1;
                        self.extract_concat_whole_low +=
                            u64::from(lo == 0 && hi == low_width.saturating_sub(1));
                    } else if lo >= low_width {
                        self.extract_concat_high_side += 1;
                        self.extract_concat_whole_high +=
                            u64::from(lo == low_width && hi == source_width.saturating_sub(1));
                    } else {
                        self.extract_concat_straddling += 1;
                    }
                }
                Op::Extract { .. } => {
                    self.extract_over_extract += 1;
                    self.max_nested_extract_depth = self
                        .max_nested_extract_depth
                        .max(nested_extract_depth(arena, source));
                }
                Op::ZeroExt { .. } => {
                    let original_width = arena.sort_of(child_args[0]).bv_width().unwrap_or(0);
                    self.record_zero_extension_extract(original_width, hi, lo);
                }
                Op::SignExt { .. } => {
                    let original_width = arena.sort_of(child_args[0]).bv_width().unwrap_or(0);
                    self.record_sign_extension_extract(original_width, hi, lo);
                }
                _ => {}
            }
        }

        fn record_zero_extension_extract(&mut self, original_width: u32, hi: u32, lo: u32) {
            self.extract_over_zero_ext += 1;
            self.low_extract_over_zero_ext +=
                u64::from(lo == 0 && hi == original_width.saturating_sub(1));
            if hi < original_width {
                self.extract_zero_ext_low_region += 1;
            } else if lo >= original_width {
                self.extract_zero_ext_high_region += 1;
            } else {
                self.extract_zero_ext_straddling += 1;
            }
        }

        fn record_sign_extension_extract(&mut self, original_width: u32, hi: u32, lo: u32) {
            self.extract_over_sign_ext += 1;
            self.low_extract_over_sign_ext +=
                u64::from(lo == 0 && hi == original_width.saturating_sub(1));
            if hi < original_width {
                self.extract_sign_ext_low_region += 1;
            } else if lo >= original_width {
                self.extract_sign_ext_high_region += 1;
            } else {
                self.extract_sign_ext_straddling += 1;
            }
        }

        fn cancellation_opportunities(&self) -> u64 {
            self.extract_over_concat
                + self.extract_over_extract
                + self.extract_over_zero_ext
                + self.extract_over_sign_ext
        }
    }

    fn nested_extract_depth(arena: &TermArena, mut term: TermId) -> u64 {
        let mut depth = 0_u64;
        while let TermNode::App {
            op: Op::Extract { .. },
            args,
        } = arena.node(term)
        {
            depth += 1;
            term = args[0];
        }
        depth
    }

    impl LayerSample {
        fn from_layers(
            layers: &BvLayerStats,
            word_preprocess: Duration,
            model_replay: Duration,
        ) -> Self {
            Self {
                word_preprocess: word_preprocess.as_secs_f64(),
                bit_blast: layers.bit_blast.as_secs_f64(),
                cnf_encode: layers.cnf_encode.as_secs_f64(),
                cnf_inprocess: layers.cnf_inprocess.as_secs_f64(),
                solve: layers.solve.as_secs_f64(),
                model_lift: layers.model_lift.as_secs_f64(),
                model_replay: model_replay.as_secs_f64(),
                aig_inputs: layers.aig_inputs,
                aig_nodes: layers.aig_nodes,
                aig_and_requests: layers.aig_and_requests,
                aig_and_trivial_simplifications: layers.aig_and_trivial_simplifications,
                aig_and_absorption_simplifications: layers.aig_and_absorption_simplifications,
                aig_and_structural_hash_hits: layers.aig_and_structural_hash_hits,
                aig_and_nodes_created: layers.aig_and_nodes_created,
                bit_demand_analysis: layers.bit_demand_analysis.as_secs_f64(),
                bit_demand_profile_complete: layers.bit_demand_profile_complete,
                bit_demand_lowering_applied: layers.bit_demand_lowering_applied,
                range_demand_decision: layers.range_demand_decision,
                range_demand_admission: layers.range_demand_admission.as_secs_f64(),
                range_demand_estimated_bits_avoided: layers.range_demand_estimated_bits_avoided,
                range_demand_analysis_work_budget: layers.range_demand_analysis_work_budget,
                range_demand_analysis_work: layers.range_demand_analysis_work,
                range_demand_merges: layers.range_demand_merges,
                range_demand_promotions: layers.range_demand_promotions,
                term_bit_requests: layers.term_bit_requests,
                term_bits_available: layers.term_bits_available,
                term_bits_demanded: layers.term_bits_demanded,
                term_bits_lowered: layers.term_bits_lowered,
                symbol_bit_requests: layers.symbol_bit_requests,
                symbol_bits_available: layers.symbol_bits_available,
                symbol_bits_demanded: layers.symbol_bits_demanded,
                symbol_bits_lowered: layers.symbol_bits_lowered,
                cnf_variables: layers.cnf_variables,
                cnf_clauses: layers.cnf_clauses,
                cnf_planning: layers.cnf_planning.as_secs_f64(),
                cnf_variable_allocation: layers.cnf_variable_allocation.as_secs_f64(),
                cnf_gate_encoding: layers.cnf_gate_encoding.as_secs_f64(),
                cnf_root_encoding: layers.cnf_root_encoding.as_secs_f64(),
                cnf_reachable_nodes: layers.cnf_reachable_nodes,
                cnf_skipped_helper_nodes: layers.cnf_skipped_helper_nodes,
                cnf_direct_root_nodes: layers.cnf_direct_root_nodes,
                cnf_xor_gates: layers.cnf_xor_gates,
                cnf_not_ite_gates: layers.cnf_not_ite_gates,
                cnf_not_and_gates: layers.cnf_not_and_gates,
                cnf_and_tree_gates: layers.cnf_and_tree_gates,
                cnf_binary_and_gates: layers.cnf_binary_and_gates,
                cnf_clause_attempts: layers.cnf_clause_attempts,
                cnf_tautological_clauses_skipped: layers.cnf_tautological_clauses_skipped,
                cnf_duplicate_clauses_skipped: layers.cnf_duplicate_clauses_skipped,
            }
        }

        fn total_s(&self) -> f64 {
            self.word_preprocess
                + self.bit_blast
                + self.cnf_encode
                + self.cnf_inprocess
                + self.solve
                + self.model_lift
                + self.model_replay
        }

        fn aig_outcomes(&self) -> u64 {
            self.aig_and_trivial_simplifications
                + self.aig_and_absorption_simplifications
                + self.aig_and_structural_hash_hits
                + self.aig_and_nodes_created
        }

        fn cnf_clause_outcomes(&self) -> u64 {
            self.cnf_clauses
                + self.cnf_tautological_clauses_skipped
                + self.cnf_duplicate_clauses_skipped
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

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum EndToEndStatus {
        NotRequested,
        NotApplicable,
        Certified,
        NotCertified,
        SatisfiableContradiction,
        RecheckFailed,
        Error,
    }

    impl EndToEndStatus {
        fn as_str(self) -> &'static str {
            match self {
                Self::NotRequested => "not-requested",
                Self::NotApplicable => "not-applicable",
                Self::Certified => "certified",
                Self::NotCertified => "not-certified",
                Self::SatisfiableContradiction => "satisfiable-contradiction",
                Self::RecheckFailed => "recheck-failed",
                Self::Error => "error",
            }
        }

        fn attempted(self) -> bool {
            !matches!(self, Self::NotRequested | Self::NotApplicable)
        }
    }

    struct EndToEndRecord {
        status: EndToEndStatus,
        elapsed: Option<Duration>,
        detail: Option<String>,
        hard_timeout: bool,
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
        end_to_end_attempted: u64,
        end_to_end_certified: u64,
        end_to_end_not_certified: u64,
        end_to_end_satisfiable_contradictions: u64,
        end_to_end_recheck_failures: u64,
        end_to_end_errors: u64,
        end_to_end_hard_timeouts: u64,
        end_to_end_s: f64,
        end_to_end_sample: Option<f64>,
        end_to_end_samples: Vec<f64>,
        end_to_end_not_certified_paths: BTreeSet<String>,
        end_to_end_hard_timeout_paths: BTreeSet<String>,
        end_to_end_alarm_paths: BTreeSet<String>,
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
        oracle_axeyum_only_decided: u64,
        oracle_z3_only_decided: u64,
        oracle_neither_decided: u64,
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
        post_word_query_shape_sample: Option<QueryShapeSample>,
        post_word_query_shape_samples: Vec<QueryShapeSample>,
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
            return match generate_corpus_manifest(&args.dir, index_path, out, args.manifest_jobs) {
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
            args.certify_end_to_end_unsat,
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
        certify_end_to_end_unsat: bool,
    ) -> ExitCode {
        eprintln!(
            "files={} sat={} unsat={} unknown={} unsupported={} errors={} \
             agree={} DISAGREE={} model_replay_failures={} \
             proof_replay_checked={} proof_replay_missing={} \
             end_to_end_certified={} end_to_end_not_certified={} \
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
            summary.end_to_end_certified,
            summary.end_to_end_not_certified,
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
        if end_to_end_summary_failed(summary, certify_end_to_end_unsat) {
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

    fn end_to_end_summary_failed(summary: &Summary, requested: bool) -> bool {
        if requested && summary.end_to_end_attempted != summary.unsat {
            eprintln!(
                "BENCHMARK INTEGRITY ALARM: end-to-end certification attempted {}/{} primary UNSAT rows",
                summary.end_to_end_attempted, summary.unsat
            );
            return true;
        }
        if summary.end_to_end_satisfiable_contradictions > 0 {
            eprintln!(
                "SOUNDNESS ALARM: end-to-end route returned satisfiable for {} primary UNSAT rows",
                summary.end_to_end_satisfiable_contradictions
            );
            return true;
        }
        if summary.end_to_end_recheck_failures > 0 {
            eprintln!(
                "SOUNDNESS ALARM: {} end-to-end certificates failed independent recheck",
                summary.end_to_end_recheck_failures
            );
            return true;
        }
        if summary.end_to_end_errors > 0 {
            eprintln!(
                "BENCHMARK INTEGRITY ALARM: {} end-to-end certification errors",
                summary.end_to_end_errors
            );
            return true;
        }
        false
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
            BackendKind::IncrementalBvBatch => Box::new(IncrementalBvBatchBackend::new()),
            BackendKind::IncrementalBvRawProfile => Box::new(IncrementalBvRawProfileBackend::new()),
            BackendKind::LazyBv => Box::new(LazyBvBackend::new()),
            BackendKind::LazyBvIte => Box::new(LazyBvBackend::new().with_abstract_ite(true)),
            BackendKind::Solver => Box::new(CheckAutoBackend::new()),
            #[cfg(feature = "z3")]
            BackendKind::Z3 => Box::new(Z3Backend::new()),
        }
    }

    /// Cold embedding adapter matching Glaurung's current fresh-solver shape,
    /// but admitting all translated roots through the shared-memo canonical
    /// batch from ADR-0156. The arena clone preserves term and symbol IDs, so
    /// both the warm solver's internal original-root replay and the harness's
    /// independent replay evaluate the untouched caller roots.
    struct IncrementalBvBatchBackend {
        stats: Option<SolveStats>,
    }

    impl IncrementalBvBatchBackend {
        fn new() -> Self {
            Self { stats: None }
        }
    }

    impl SolverBackend for IncrementalBvBatchBackend {
        fn capabilities(&self) -> Capabilities {
            Capabilities {
                name: "axeyum-incremental-bv canonical-batch-v1".to_owned(),
                produces_models: true,
                complete: true,
            }
        }

        fn check(
            &mut self,
            arena: &TermArena,
            assertions: &[TermId],
            config: &SolverConfig,
        ) -> Result<CheckResult, SolverError> {
            let mut owned = arena.clone();
            let mut solver = IncrementalBvSolver::with_config(config.clone());
            let translate_start = Instant::now();
            let lowered = solver.assert_preprocessed_batch(&mut owned, assertions)?;
            let translate = translate_start.elapsed();
            let solve_start = Instant::now();
            let result = solver.check(&owned);
            let solve = solve_start.elapsed();
            let terms_translated = TermStats::compute(&owned, &lowered).dag_nodes;
            let mut stats = SolveStats::default();
            stats.translate = translate;
            stats.solve = solve;
            stats.assertion_count = usize_to_u64(assertions.len());
            stats.terms_translated = terms_translated;
            stats.backend = vec![
                (
                    "incremental_aig_nodes".to_owned(),
                    usize_to_f64(solver.lowered_aig_node_count()),
                ),
                (
                    "incremental_cnf_variables".to_owned(),
                    usize_to_f64(solver.encoded_variable_count()),
                ),
                (
                    "incremental_cnf_clauses".to_owned(),
                    usize_to_f64(solver.encoded_clause_count()),
                ),
            ];
            self.stats = Some(stats);
            result
        }

        fn last_stats(&self) -> Option<&SolveStats> {
            self.stats.as_ref()
        }
    }

    /// Diagnostic adapter matching Glaurung's fresh raw arena/solver/assertion
    /// policy while exposing the opt-in incremental gate mix. The shape scan is
    /// intentionally charged to this backend, so its timing is attribution-only
    /// and must not be compared with ordinary `incremental-bv-batch` timing.
    struct IncrementalBvRawProfileBackend {
        stats: Option<SolveStats>,
    }

    impl IncrementalBvRawProfileBackend {
        fn new() -> Self {
            Self { stats: None }
        }
    }

    impl SolverBackend for IncrementalBvRawProfileBackend {
        fn capabilities(&self) -> Capabilities {
            Capabilities {
                name: "axeyum-incremental-bv raw-profile-v1".to_owned(),
                produces_models: true,
                complete: true,
            }
        }

        fn check(
            &mut self,
            arena: &TermArena,
            assertions: &[TermId],
            config: &SolverConfig,
        ) -> Result<CheckResult, SolverError> {
            let mut raw_config = config.clone();
            raw_config.preprocess = false;
            let mut solver = IncrementalBvSolver::with_config_and_profiling(raw_config);
            let translate_start = Instant::now();
            for &assertion in assertions {
                solver.assert(arena, assertion)?;
            }
            let translate = translate_start.elapsed();
            let solve_start = Instant::now();
            let result = solver.check(arena);
            let solve = solve_start.elapsed();
            let profile = solver.stats();
            let mut stats = SolveStats::default();
            stats.translate = translate;
            stats.solve = solve;
            stats.assertion_count = usize_to_u64(assertions.len());
            stats.terms_translated = TermStats::compute(arena, assertions).dag_nodes;
            stats.backend = incremental_gate_mix_backend_stats(&profile);
            self.stats = Some(stats);
            result
        }

        fn last_stats(&self) -> Option<&SolveStats> {
            self.stats.as_ref()
        }
    }

    fn incremental_gate_mix_backend_stats(profile: &IncrementalBvStats) -> Vec<(String, f64)> {
        let gate_mix = profile.cnf_gate_mix;
        let mut stats = vec![
            (
                "incremental_aig_nodes".to_owned(),
                u64_to_f64(profile.aig_nodes),
            ),
            (
                "incremental_cnf_variables".to_owned(),
                u64_to_f64(profile.cnf_variables),
            ),
            (
                "incremental_cnf_clauses".to_owned(),
                u64_to_f64(profile.cnf_clauses),
            ),
            (
                "incremental_cnf_and_nodes_synced".to_owned(),
                u64_to_f64(gate_mix.and_nodes_synced),
            ),
            (
                "incremental_cnf_up_half_definitions".to_owned(),
                u64_to_f64(gate_mix.up_half_definitions),
            ),
            (
                "incremental_cnf_down_half_definitions".to_owned(),
                u64_to_f64(gate_mix.down_half_definitions),
            ),
            (
                "incremental_cnf_xor_half_definitions".to_owned(),
                u64_to_f64(gate_mix.xor_half_definitions),
            ),
            (
                "incremental_cnf_not_ite_half_definitions".to_owned(),
                u64_to_f64(gate_mix.not_ite_half_definitions),
            ),
            (
                "incremental_cnf_not_and_half_definitions".to_owned(),
                u64_to_f64(gate_mix.not_and_half_definitions),
            ),
            (
                "incremental_cnf_and_tree_half_definitions".to_owned(),
                u64_to_f64(gate_mix.and_tree_half_definitions),
            ),
            (
                "incremental_cnf_binary_and_half_definitions".to_owned(),
                u64_to_f64(gate_mix.binary_and_half_definitions),
            ),
            (
                "incremental_cnf_constant_clauses".to_owned(),
                u64_to_f64(gate_mix.constant_clauses),
            ),
            (
                "incremental_cnf_definition_clauses".to_owned(),
                u64_to_f64(gate_mix.definition_clauses),
            ),
            (
                "incremental_cnf_root_clauses".to_owned(),
                u64_to_f64(gate_mix.root_clauses),
            ),
            (
                "incremental_cnf_direct_positive_and_roots".to_owned(),
                u64_to_f64(gate_mix.direct_positive_and_roots),
            ),
            (
                "incremental_cnf_direct_positive_and_nodes".to_owned(),
                u64_to_f64(gate_mix.direct_positive_and_nodes),
            ),
            (
                "incremental_cnf_direct_positive_and_leaves".to_owned(),
                u64_to_f64(gate_mix.direct_positive_and_leaves),
            ),
            (
                "incremental_cnf_direct_xor_leaves".to_owned(),
                u64_to_f64(gate_mix.direct_xor_leaves),
            ),
            (
                "incremental_cnf_direct_not_ite_leaves".to_owned(),
                u64_to_f64(gate_mix.direct_not_ite_leaves),
            ),
            (
                "incremental_cnf_direct_negative_and_roots".to_owned(),
                u64_to_f64(gate_mix.direct_negative_and_roots),
            ),
            (
                "incremental_cnf_fused_positive_and_roots".to_owned(),
                u64_to_f64(gate_mix.fused_positive_and_roots),
            ),
            (
                "incremental_cnf_fused_positive_and_nodes".to_owned(),
                u64_to_f64(gate_mix.fused_positive_and_nodes),
            ),
            (
                "incremental_cnf_fused_xor_leaves".to_owned(),
                u64_to_f64(gate_mix.fused_xor_leaves),
            ),
        ];
        stats.extend(incremental_root_residual_backend_stats(&gate_mix));
        stats
    }

    fn incremental_root_residual_backend_stats(
        gate_mix: &axeyum_solver::IncrementalCnfStats,
    ) -> Vec<(String, f64)> {
        vec![
            (
                "incremental_cnf_root_assertions".to_owned(),
                u64_to_f64(gate_mix.root_assertions),
            ),
            (
                "incremental_cnf_guarded_root_assertions".to_owned(),
                u64_to_f64(gate_mix.guarded_root_assertions),
            ),
            (
                "incremental_cnf_repeated_same_context_roots".to_owned(),
                u64_to_f64(gate_mix.repeated_same_context_roots),
            ),
            (
                "incremental_cnf_deduplicated_root_assertions".to_owned(),
                u64_to_f64(gate_mix.deduplicated_root_assertions),
            ),
            (
                "incremental_cnf_reused_cross_context_roots".to_owned(),
                u64_to_f64(gate_mix.reused_cross_context_roots),
            ),
            (
                "incremental_cnf_guarded_root_clauses".to_owned(),
                u64_to_f64(gate_mix.guarded_root_clauses),
            ),
            (
                "incremental_cnf_root_clause_attempts".to_owned(),
                u64_to_f64(gate_mix.root_clause_attempts),
            ),
            (
                "incremental_cnf_unit_payload_root_clauses".to_owned(),
                u64_to_f64(gate_mix.unit_payload_root_clauses),
            ),
            (
                "incremental_cnf_binary_payload_root_clauses".to_owned(),
                u64_to_f64(gate_mix.binary_payload_root_clauses),
            ),
            (
                "incremental_cnf_wide_payload_root_clauses".to_owned(),
                u64_to_f64(gate_mix.wide_payload_root_clauses),
            ),
            (
                "incremental_cnf_duplicate_definition_clauses".to_owned(),
                u64_to_f64(gate_mix.duplicate_definition_clauses),
            ),
            (
                "incremental_cnf_duplicate_root_clauses".to_owned(),
                u64_to_f64(gate_mix.duplicate_root_clauses),
            ),
            (
                "incremental_cnf_duplicate_prior_root_clauses".to_owned(),
                u64_to_f64(gate_mix.duplicate_prior_root_clauses),
            ),
            (
                "incremental_cnf_root_clauses_duplicate_non_root".to_owned(),
                u64_to_f64(gate_mix.root_clauses_duplicate_non_root),
            ),
            (
                "incremental_cnf_tautological_definition_clauses".to_owned(),
                u64_to_f64(gate_mix.tautological_definition_clauses),
            ),
            (
                "incremental_cnf_tautological_root_clauses".to_owned(),
                u64_to_f64(gate_mix.tautological_root_clauses),
            ),
            (
                "incremental_cnf_fresh_negative_root_definitions".to_owned(),
                u64_to_f64(gate_mix.fresh_negative_root_definitions),
            ),
            (
                "incremental_cnf_reused_negative_root_definitions".to_owned(),
                u64_to_f64(gate_mix.reused_negative_root_definitions),
            ),
        ]
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
    fn rewrite_summary_record(s: &Summary, args: &Args, instances: &[JsonValue]) -> JsonValue {
        json!({
            "mode": args.rewrite.as_str(),
            "disabled_rule_ids": args.rewrite_disabled_rules.iter().collect::<BTreeSet<_>>(),
            "changed_instances": s.rewrite_changed_instances,
            "applications": s.rewrite_applications,
            "input_dag_nodes": s.rewrite_input_dag_nodes,
            "output_dag_nodes": s.rewrite_output_dag_nodes,
            "input_tree_nodes": s.rewrite_input_tree_nodes,
            "output_tree_nodes": s.rewrite_output_tree_nodes,
            "decision_matches": s.rewrite_decision_matches,
            "decision_changes": s.rewrite_decision_changes,
            "sat_unsat_conflicts": s.rewrite_sat_unsat_conflicts,
            "per_rule": rewrite_rule_attribution_record(instances),
        })
    }

    #[derive(Default)]
    struct RewriteRuleAttribution {
        applications: u64,
        affected_instances: u64,
        affected_families: BTreeMap<String, u64>,
        input_dag_nodes: u64,
        output_dag_nodes: u64,
        input_tree_nodes: u64,
        output_tree_nodes: u64,
        output_aig_nodes: u64,
        output_cnf_variables: u64,
        output_cnf_clauses: u64,
        output_cold_ms: f64,
    }

    fn rewrite_rule_attribution_record(instances: &[JsonValue]) -> JsonValue {
        let mut rules = BTreeMap::<String, RewriteRuleAttribution>::new();
        for instance in instances {
            let Some(rule_counts) = instance
                .get("rewrite")
                .and_then(|rewrite| rewrite.get("rule_counts"))
                .and_then(JsonValue::as_object)
            else {
                continue;
            };
            let family = instance
                .get("corpus_manifest")
                .and_then(|manifest| manifest.get("family"))
                .and_then(JsonValue::as_str)
                .unwrap_or("unmanifested");
            let rewrite = &instance["rewrite"];
            let layers = &instance["layer_attribution"];
            for (rule_id, count) in rule_counts {
                let Some(count) = count.as_u64() else {
                    continue;
                };
                let entry = rules.entry(rule_id.clone()).or_default();
                entry.applications = entry.applications.saturating_add(count);
                entry.affected_instances = entry.affected_instances.saturating_add(1);
                *entry
                    .affected_families
                    .entry(family.to_owned())
                    .or_insert(0) += 1;
                entry.input_dag_nodes = entry
                    .input_dag_nodes
                    .saturating_add(json_u64(rewrite, "input_dag_nodes"));
                entry.output_dag_nodes = entry
                    .output_dag_nodes
                    .saturating_add(json_u64(rewrite, "output_dag_nodes"));
                entry.input_tree_nodes = entry
                    .input_tree_nodes
                    .saturating_add(json_u64(rewrite, "input_tree_nodes"));
                entry.output_tree_nodes = entry
                    .output_tree_nodes
                    .saturating_add(json_u64(rewrite, "output_tree_nodes"));
                entry.output_aig_nodes = entry
                    .output_aig_nodes
                    .saturating_add(json_u64(layers, "aig_nodes"));
                entry.output_cnf_variables = entry
                    .output_cnf_variables
                    .saturating_add(json_u64(layers, "cnf_variables"));
                entry.output_cnf_clauses = entry
                    .output_cnf_clauses
                    .saturating_add(json_u64(layers, "cnf_clauses"));
                entry.output_cold_ms += instance
                    .get("cold_total_ms")
                    .and_then(JsonValue::as_f64)
                    .unwrap_or(0.0);
            }
        }
        let rules = rules
            .into_iter()
            .map(|(rule_id, entry)| {
                let dag_removed = entry.input_dag_nodes.saturating_sub(entry.output_dag_nodes);
                let tree_removed = entry
                    .input_tree_nodes
                    .saturating_sub(entry.output_tree_nodes);
                (
                    rule_id,
                    json!({
                        "applications": entry.applications,
                        "affected_instances": entry.affected_instances,
                        "affected_families": entry.affected_families,
                        "input_dag_nodes": entry.input_dag_nodes,
                        "output_dag_nodes": entry.output_dag_nodes,
                        "dag_nodes_removed": dag_removed,
                        "input_tree_nodes": entry.input_tree_nodes,
                        "output_tree_nodes": entry.output_tree_nodes,
                        "tree_nodes_removed": tree_removed,
                        "selected_policy_output": {
                            "aig_nodes": entry.output_aig_nodes,
                            "cnf_variables": entry.output_cnf_variables,
                            "cnf_clauses": entry.output_cnf_clauses,
                            "cold_total_ms": entry.output_cold_ms,
                        },
                    }),
                )
            })
            .collect::<BTreeMap<_, _>>();
        json!({
            "counting_unit": "one affected instance per rule; instances firing multiple rules appear in each rule bucket",
            "selected_policy_output_is_not_saved_work": true,
            "ablation_contract": "pair this artifact by manifest path with --rewrite default --rewrite-disable-rule <id> to measure causal AIG/CNF/time deltas",
            "rules": rules,
        })
    }

    fn json_u64(record: &JsonValue, field: &str) -> u64 {
        record.get(field).and_then(JsonValue::as_u64).unwrap_or(0)
    }

    #[allow(clippy::cast_precision_loss)]
    fn timing_distribution_record<T>(
        samples: &[T],
        select_seconds: impl Fn(&T) -> f64,
    ) -> JsonValue {
        if samples.is_empty() {
            return JsonValue::Null;
        }
        let mut values = samples.iter().map(select_seconds).collect::<Vec<_>>();
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
    fn count_distribution_record<T>(samples: &[T], select: impl Fn(&T) -> u64) -> JsonValue {
        if samples.is_empty() {
            return JsonValue::Null;
        }
        let mut values = samples.iter().map(select).collect::<Vec<_>>();
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

    fn sum_shape(samples: &[QueryShapeSample], select: impl Fn(&QueryShapeSample) -> u64) -> u64 {
        samples.iter().map(select).fold(0, u64::saturating_add)
    }

    fn qfbv_operator_record(counts: &QfBvOperatorCounts) -> JsonValue {
        json!({
            "applications": counts.applications(),
            "boolean": {
                "not": counts.bool_not,
                "and": counts.bool_and,
                "or": counts.bool_or,
                "xor": counts.bool_xor,
                "implies": counts.bool_implies,
            },
            "bit_vector": {
                "bitwise": {
                    "not": counts.bv_not,
                    "and": counts.bv_and,
                    "or": counts.bv_or,
                    "xor": counts.bv_xor,
                    "nand": counts.bv_nand,
                    "nor": counts.bv_nor,
                    "xnor": counts.bv_xnor,
                },
                "arithmetic": {
                    "neg": counts.bv_neg,
                    "add": counts.bv_add,
                    "sub": counts.bv_sub,
                    "mul": counts.bv_mul,
                    "udiv": counts.bv_udiv,
                    "urem": counts.bv_urem,
                    "sdiv": counts.bv_sdiv,
                    "srem": counts.bv_srem,
                    "smod": counts.bv_smod,
                },
                "shifts": {
                    "shl": counts.bv_shl,
                    "lshr": counts.bv_lshr,
                    "ashr": counts.bv_ashr,
                },
                "comparisons": {
                    "ult": counts.bv_ult,
                    "ule": counts.bv_ule,
                    "ugt": counts.bv_ugt,
                    "uge": counts.bv_uge,
                    "slt": counts.bv_slt,
                    "sle": counts.bv_sle,
                    "sgt": counts.bv_sgt,
                    "sge": counts.bv_sge,
                },
                "structural": {
                    "comp": counts.bv_comp,
                    "extract": counts.extract,
                    "concat": counts.concat,
                    "zero_extend": counts.zero_extend,
                    "sign_extend": counts.sign_extend,
                    "rotate_left": counts.rotate_left,
                    "rotate_right": counts.rotate_right,
                },
            },
            "polymorphic": {
                "eq": counts.eq,
                "ite": counts.ite,
            },
            "other": counts.other,
        })
    }

    fn qfbv_operator_totals(samples: &[QueryShapeSample]) -> QfBvOperatorCounts {
        let mut totals = QfBvOperatorCounts::default();
        for sample in samples {
            totals.merge(sample.qfbv_operators);
        }
        totals
    }

    fn query_shape_snapshot_record(sample: &QueryShapeSample, counting_unit: &str) -> JsonValue {
        json!({
            "counting_unit": counting_unit,
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
            "qfbv_operator_inventory": qfbv_operator_record(&sample.qfbv_operators),
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
                "exact_low_extract_over_sign_extend": sample.low_extract_over_sign_ext,
                "concat_regions": {
                    "low_side": sample.extract_concat_low_side,
                    "high_side": sample.extract_concat_high_side,
                    "straddling": sample.extract_concat_straddling,
                    "whole_low_operand": sample.extract_concat_whole_low,
                    "whole_high_operand": sample.extract_concat_whole_high,
                },
                "zero_extend_regions": {
                    "low": sample.extract_zero_ext_low_region,
                    "high": sample.extract_zero_ext_high_region,
                    "straddling": sample.extract_zero_ext_straddling,
                },
                "sign_extend_regions": {
                    "low": sample.extract_sign_ext_low_region,
                    "high": sample.extract_sign_ext_high_region,
                    "straddling": sample.extract_sign_ext_straddling,
                },
                "max_nested_extract_depth": sample.max_nested_extract_depth,
            },
        })
    }

    fn opportunity_change(before: u64, after: u64) -> JsonValue {
        json!({
            "before": before,
            "after": after,
            "removed": before.saturating_sub(after),
            "added": after.saturating_sub(before),
        })
    }

    fn opportunity_transition_record(
        before: &[QueryShapeSample],
        after: &[QueryShapeSample],
    ) -> JsonValue {
        let transition = |select: fn(&QueryShapeSample) -> u64| {
            opportunity_change(sum_shape(before, select), sum_shape(after, select))
        };
        json!({
            "counting_unit": "unique reachable DAG opportunities before and after the selected word policy",
            "total": transition(QueryShapeSample::cancellation_opportunities),
            "extract_over_concat": transition(|sample| sample.extract_over_concat),
            "extract_over_extract": transition(|sample| sample.extract_over_extract),
            "extract_over_zero_extend": transition(|sample| sample.extract_over_zero_ext),
            "extract_over_sign_extend": transition(|sample| sample.extract_over_sign_ext),
            "exact_low_extract_over_zero_extend": transition(
                |sample| sample.low_extract_over_zero_ext,
            ),
            "exact_low_extract_over_sign_extend": transition(
                |sample| sample.low_extract_over_sign_ext,
            ),
            "concat_regions": {
                "low_side": transition(|sample| sample.extract_concat_low_side),
                "high_side": transition(|sample| sample.extract_concat_high_side),
                "straddling": transition(|sample| sample.extract_concat_straddling),
                "whole_low_operand": transition(|sample| sample.extract_concat_whole_low),
                "whole_high_operand": transition(|sample| sample.extract_concat_whole_high),
            },
            "zero_extend_regions": {
                "low": transition(|sample| sample.extract_zero_ext_low_region),
                "high": transition(|sample| sample.extract_zero_ext_high_region),
                "straddling": transition(|sample| sample.extract_zero_ext_straddling),
            },
            "sign_extend_regions": {
                "low": transition(|sample| sample.extract_sign_ext_low_region),
                "high": transition(|sample| sample.extract_sign_ext_high_region),
                "straddling": transition(|sample| sample.extract_sign_ext_straddling),
            },
        })
    }

    fn query_shape_record(original: &QueryShapeSample, post_word: &QueryShapeSample) -> JsonValue {
        let mut record = query_shape_snapshot_record(original, "unique original-query DAG nodes");
        if let JsonValue::Object(object) = &mut record {
            object.insert(
                "post_word_policy".to_owned(),
                query_shape_snapshot_record(post_word, "unique post-word-policy DAG nodes"),
            );
            object.insert(
                "opportunity_transition".to_owned(),
                opportunity_transition_record(
                    std::slice::from_ref(original),
                    std::slice::from_ref(post_word),
                ),
            );
        }
        record
    }

    fn coercion_opportunity_totals_record(samples: &[QueryShapeSample]) -> JsonValue {
        json!({
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
            "exact_low_extract_over_sign_extend": sum_shape(
                samples,
                |sample| sample.low_extract_over_sign_ext,
            ),
            "concat_regions": {
                "low_side": sum_shape(samples, |sample| sample.extract_concat_low_side),
                "high_side": sum_shape(samples, |sample| sample.extract_concat_high_side),
                "straddling": sum_shape(samples, |sample| sample.extract_concat_straddling),
                "whole_low_operand": sum_shape(
                    samples,
                    |sample| sample.extract_concat_whole_low,
                ),
                "whole_high_operand": sum_shape(
                    samples,
                    |sample| sample.extract_concat_whole_high,
                ),
            },
            "zero_extend_regions": {
                "low": sum_shape(samples, |sample| sample.extract_zero_ext_low_region),
                "high": sum_shape(samples, |sample| sample.extract_zero_ext_high_region),
                "straddling": sum_shape(
                    samples,
                    |sample| sample.extract_zero_ext_straddling,
                ),
            },
            "sign_extend_regions": {
                "low": sum_shape(samples, |sample| sample.extract_sign_ext_low_region),
                "high": sum_shape(samples, |sample| sample.extract_sign_ext_high_region),
                "straddling": sum_shape(
                    samples,
                    |sample| sample.extract_sign_ext_straddling,
                ),
            },
            "max_nested_extract_depth": samples
                .iter()
                .map(|sample| sample.max_nested_extract_depth)
                .max()
                .unwrap_or(0),
        })
    }

    fn query_shape_aggregate_record(
        samples: &[QueryShapeSample],
        profiled_instances: u64,
        counting_unit: &str,
    ) -> JsonValue {
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
            "profiled_instances": profiled_instances,
            "counting_unit": counting_unit,
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
            "qfbv_operator_totals": qfbv_operator_record(&qfbv_operator_totals(samples)),
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
                "bv_add_sub": count_distribution_record(
                    samples,
                    |sample| sample.qfbv_operators.bv_add + sample.qfbv_operators.bv_sub,
                ),
                "bv_bitwise": count_distribution_record(samples, |sample| {
                    let counts = sample.qfbv_operators;
                    counts.bv_not
                        + counts.bv_and
                        + counts.bv_or
                        + counts.bv_xor
                        + counts.bv_nand
                        + counts.bv_nor
                        + counts.bv_xnor
                }),
                "bv_comparisons": count_distribution_record(samples, |sample| {
                    let counts = sample.qfbv_operators;
                    counts.bv_ult
                        + counts.bv_ule
                        + counts.bv_ugt
                        + counts.bv_uge
                        + counts.bv_slt
                        + counts.bv_sle
                        + counts.bv_sgt
                        + counts.bv_sge
                }),
                "ite": count_distribution_record(samples, |sample| {
                    sample.qfbv_operators.ite
                }),
            },
            "extract_demand": {
                "result_bits": extract_result_bits,
                "source_bits": extract_source_bits,
                "result_over_source_ratio": demand_ratio,
                "narrow_extracts": sum_shape(samples, |sample| sample.narrow_extracts),
            },
            "coercion_cancellation_opportunities": coercion_opportunity_totals_record(samples),
            "memory_provenance": {
                "surviving_select_store_ops": sum_shape(
                    samples,
                    |sample| sample.selects + sample.stores,
                ),
                "limitation": "memory-derived provenance flattened to BV terms is not inferable; retain it in manifest family/source metadata",
            },
        })
    }

    fn query_shape_summary_record(s: &Summary) -> JsonValue {
        let original = &s.query_shape_samples;
        if original.is_empty() {
            return JsonValue::Null;
        }
        let post_word = &s.post_word_query_shape_samples;
        let mut record = query_shape_aggregate_record(
            original,
            s.query_shape_files,
            "unique original-query DAG nodes",
        );
        if let JsonValue::Object(object) = &mut record {
            let complete = post_word.len() == original.len();
            object.insert("post_word_profile_complete".to_owned(), json!(complete));
            object.insert(
                "post_word_policy".to_owned(),
                if complete {
                    query_shape_aggregate_record(
                        post_word,
                        usize_to_u64(post_word.len()),
                        "unique post-word-policy DAG nodes",
                    )
                } else {
                    JsonValue::Null
                },
            );
            object.insert(
                "opportunity_transition".to_owned(),
                if complete {
                    opportunity_transition_record(original, post_word)
                } else {
                    JsonValue::Null
                },
            );
        }
        record
    }

    fn construction_attribution_record(samples: &[LayerSample]) -> JsonValue {
        let count = |select: fn(&LayerSample) -> u64| {
            samples.iter().map(select).fold(0_u64, u64::saturating_add)
        };
        let seconds = |select: fn(&LayerSample) -> f64| samples.iter().map(select).sum::<f64>();

        let aig_requests = count(|sample| sample.aig_and_requests);
        let aig_outcomes = count(LayerSample::aig_outcomes);
        let cnf_attempts = count(|sample| sample.cnf_clause_attempts);
        let cnf_clause_outcomes = count(LayerSample::cnf_clause_outcomes);
        json!({
            "cnf_subphases_are_nested_in_cnf_encode": true,
            "aig": {
                "and_requests": aig_requests,
                "trivial_simplifications": count(
                    |sample| sample.aig_and_trivial_simplifications,
                ),
                "absorption_simplifications": count(
                    |sample| sample.aig_and_absorption_simplifications,
                ),
                "structural_hash_hits": count(
                    |sample| sample.aig_and_structural_hash_hits,
                ),
                "nodes_created": count(|sample| sample.aig_and_nodes_created),
                "request_outcomes_partition_requests": aig_outcomes == aig_requests,
            },
            "cnf": {
                "subphase_s": {
                    "planning": seconds(|sample| sample.cnf_planning),
                    "variable_allocation": seconds(
                        |sample| sample.cnf_variable_allocation,
                    ),
                    "gate_encoding": seconds(|sample| sample.cnf_gate_encoding),
                    "root_encoding": seconds(|sample| sample.cnf_root_encoding),
                },
                "subphase_distributions": {
                    "planning": timing_distribution_record(
                        samples,
                        |sample| sample.cnf_planning,
                    ),
                    "variable_allocation": timing_distribution_record(
                        samples,
                        |sample| sample.cnf_variable_allocation,
                    ),
                    "gate_encoding": timing_distribution_record(
                        samples,
                        |sample| sample.cnf_gate_encoding,
                    ),
                    "root_encoding": timing_distribution_record(
                        samples,
                        |sample| sample.cnf_root_encoding,
                    ),
                },
                "reachable_nodes": count(|sample| sample.cnf_reachable_nodes),
                "skipped_helper_nodes": count(|sample| sample.cnf_skipped_helper_nodes),
                "direct_root_nodes": count(|sample| sample.cnf_direct_root_nodes),
                "gate_families": {
                    "xor": count(|sample| sample.cnf_xor_gates),
                    "not_ite": count(|sample| sample.cnf_not_ite_gates),
                    "not_and": count(|sample| sample.cnf_not_and_gates),
                    "and_tree": count(|sample| sample.cnf_and_tree_gates),
                    "binary_and": count(|sample| sample.cnf_binary_and_gates),
                },
                "clause_attempts": cnf_attempts,
                "tautological_clauses_skipped": count(
                    |sample| sample.cnf_tautological_clauses_skipped,
                ),
                "duplicate_clauses_skipped": count(
                    |sample| sample.cnf_duplicate_clauses_skipped,
                ),
                "clauses_emitted": count(|sample| sample.cnf_clauses),
                "clause_outcomes_partition_attempts": cnf_clause_outcomes == cnf_attempts,
            },
        })
    }

    #[allow(clippy::too_many_lines)] // Flat versioned JSON contract; keep profile modes adjacent.
    fn bit_demand_attribution_record(samples: &[LayerSample]) -> JsonValue {
        let count = |select: fn(&LayerSample) -> u64| {
            samples.iter().map(select).fold(0_u64, u64::saturating_add)
        };
        let term_requests = count(|sample| sample.term_bit_requests);
        let term_available = count(|sample| sample.term_bits_available);
        let term_demanded = count(|sample| sample.term_bits_demanded);
        let term_lowered = count(|sample| sample.term_bits_lowered);
        let symbol_requests = count(|sample| sample.symbol_bit_requests);
        let symbol_available = count(|sample| sample.symbol_bits_available);
        let symbol_demanded = count(|sample| sample.symbol_bits_demanded);
        let symbol_lowered = count(|sample| sample.symbol_bits_lowered);
        let complete_samples = samples
            .iter()
            .filter(|sample| sample.bit_demand_profile_complete)
            .count();
        let lowering_samples = samples
            .iter()
            .filter(|sample| sample.bit_demand_lowering_applied)
            .count();
        let profile_complete = !samples.is_empty() && complete_samples == samples.len();
        let range = range_demand_attribution_record(samples);
        if !profile_complete {
            let profile_mode = if complete_samples == 0 {
                "off"
            } else {
                "mixed"
            };
            return json!({
                "profile_complete": false,
                "profile_mode": profile_mode,
                "lowering_applied": false,
                "lowering_applied_samples": lowering_samples,
                "analysis_is_nested_in_bit_blast": true,
                "analysis_s": samples.iter().map(|sample| sample.bit_demand_analysis).sum::<f64>(),
                "analysis_distribution": JsonValue::Null,
                "range": range,
                "term": {
                    "requests": JsonValue::Null,
                    "available": JsonValue::Null,
                    "demanded": JsonValue::Null,
                    "lowered": term_lowered,
                    "demanded_over_available": JsonValue::Null,
                    "lowered_over_demanded": JsonValue::Null,
                    "requests_cover_demanded": JsonValue::Null,
                    "demanded_within_available": JsonValue::Null,
                    "lowering_covers_demanded": JsonValue::Null,
                },
                "symbol": {
                    "requests": JsonValue::Null,
                    "available": JsonValue::Null,
                    "demanded": JsonValue::Null,
                    "lowered": symbol_lowered,
                    "demanded_over_available": JsonValue::Null,
                    "lowered_over_demanded": JsonValue::Null,
                    "requests_cover_demanded": JsonValue::Null,
                    "demanded_within_available": JsonValue::Null,
                    "lowering_covers_demanded": JsonValue::Null,
                },
            });
        }
        let lowering_applied = lowering_samples == samples.len();
        let profile_mode = if lowering_applied {
            "structural-lowering"
        } else if lowering_samples == 0 {
            "structural-observational"
        } else {
            "mixed"
        };
        json!({
            "profile_complete": true,
            "profile_mode": profile_mode,
            "lowering_applied": lowering_applied,
            "lowering_applied_samples": lowering_samples,
            "analysis_is_nested_in_bit_blast": true,
            "analysis_s": samples.iter().map(|sample| sample.bit_demand_analysis).sum::<f64>(),
            "analysis_distribution": timing_distribution_record(
                samples,
                |sample| sample.bit_demand_analysis,
            ),
            "range": range,
            "term": {
                "requests": term_requests,
                "available": term_available,
                "demanded": term_demanded,
                "lowered": term_lowered,
                "demanded_over_available": ratio_record(term_demanded, term_available),
                "lowered_over_demanded": ratio_record(term_lowered, term_demanded),
                "requests_cover_demanded": term_requests >= term_demanded,
                "demanded_within_available": term_demanded <= term_available,
                "lowering_covers_demanded": term_lowered >= term_demanded,
            },
            "symbol": {
                "requests": symbol_requests,
                "available": symbol_available,
                "demanded": symbol_demanded,
                "lowered": symbol_lowered,
                "demanded_over_available": ratio_record(symbol_demanded, symbol_available),
                "lowered_over_demanded": ratio_record(symbol_lowered, symbol_demanded),
                "requests_cover_demanded": symbol_requests >= symbol_demanded,
                "demanded_within_available": symbol_demanded <= symbol_available,
                "lowering_covers_demanded": symbol_lowered >= symbol_demanded,
            },
        })
    }

    fn range_demand_attribution_record(samples: &[LayerSample]) -> JsonValue {
        let decisions = [
            RangeDemandDecision::NotRequested,
            RangeDemandDecision::NoCandidate,
            RangeDemandDecision::InsufficientEstimate,
            RangeDemandDecision::AnalysisBudgetExceeded,
            RangeDemandDecision::InsufficientExactSavings,
            RangeDemandDecision::Applied,
        ];
        let decision_counts = decisions
            .into_iter()
            .map(|decision| {
                (
                    decision.as_str().to_owned(),
                    json!(
                        samples
                            .iter()
                            .filter(|sample| sample.range_demand_decision == decision)
                            .count()
                    ),
                )
            })
            .collect::<serde_json::Map<_, _>>();
        let count = |select: fn(&LayerSample) -> u64| {
            samples.iter().map(select).fold(0_u64, u64::saturating_add)
        };
        let work = count(|sample| sample.range_demand_analysis_work);
        let budget = count(|sample| sample.range_demand_analysis_work_budget);
        json!({
            "decision_counts": decision_counts,
            "admission_s": samples.iter().map(|sample| sample.range_demand_admission).sum::<f64>(),
            "admission_distribution": timing_distribution_record(
                samples,
                |sample| sample.range_demand_admission,
            ),
            "estimated_bits_avoided": count(
                |sample| sample.range_demand_estimated_bits_avoided,
            ),
            "analysis_work": work,
            "analysis_work_budget": budget,
            "analysis_work_within_budget": work <= budget,
            "range_merges": count(|sample| sample.range_demand_merges),
            "range_promotions": count(|sample| sample.range_demand_promotions),
        })
    }

    #[allow(clippy::cast_precision_loss)]
    fn ratio_record(numerator: u64, denominator: u64) -> JsonValue {
        if denominator == 0 {
            JsonValue::Null
        } else {
            json!(numerator as f64 / denominator as f64)
        }
    }

    fn instance_bit_demand_record(sample: &LayerSample) -> JsonValue {
        let range = json!({
            "decision": sample.range_demand_decision.as_str(),
            "admission_ms": sample.range_demand_admission * 1000.0,
            "estimated_bits_avoided": sample.range_demand_estimated_bits_avoided,
            "analysis_work": sample.range_demand_analysis_work,
            "analysis_work_budget": sample.range_demand_analysis_work_budget,
            "analysis_work_within_budget":
                sample.range_demand_analysis_work <= sample.range_demand_analysis_work_budget,
            "range_merges": sample.range_demand_merges,
            "range_promotions": sample.range_demand_promotions,
        });
        if !sample.bit_demand_profile_complete {
            return json!({
                "profile_complete": false,
                "profile_mode": "off",
                "lowering_applied": false,
                "analysis_is_nested_in_bit_blast": true,
                "analysis_ms": sample.bit_demand_analysis * 1000.0,
                "range": range,
                "term": {
                    "requests": JsonValue::Null,
                    "available": JsonValue::Null,
                    "demanded": JsonValue::Null,
                    "lowered": sample.term_bits_lowered,
                    "demanded_over_available": JsonValue::Null,
                    "lowered_over_demanded": JsonValue::Null,
                    "requests_cover_demanded": JsonValue::Null,
                    "demanded_within_available": JsonValue::Null,
                    "lowering_covers_demanded": JsonValue::Null,
                },
                "symbol": {
                    "requests": JsonValue::Null,
                    "available": JsonValue::Null,
                    "demanded": JsonValue::Null,
                    "lowered": sample.symbol_bits_lowered,
                    "demanded_over_available": JsonValue::Null,
                    "lowered_over_demanded": JsonValue::Null,
                    "requests_cover_demanded": JsonValue::Null,
                    "demanded_within_available": JsonValue::Null,
                    "lowering_covers_demanded": JsonValue::Null,
                },
            });
        }
        json!({
            "profile_complete": true,
            "profile_mode": if sample.bit_demand_lowering_applied {
                "structural-lowering"
            } else {
                "structural-observational"
            },
            "lowering_applied": sample.bit_demand_lowering_applied,
            "analysis_is_nested_in_bit_blast": true,
            "analysis_ms": sample.bit_demand_analysis * 1000.0,
            "range": range,
            "term": {
                "requests": sample.term_bit_requests,
                "available": sample.term_bits_available,
                "demanded": sample.term_bits_demanded,
                "lowered": sample.term_bits_lowered,
                "demanded_over_available": ratio_record(
                    sample.term_bits_demanded,
                    sample.term_bits_available,
                ),
                "lowered_over_demanded": ratio_record(
                    sample.term_bits_lowered,
                    sample.term_bits_demanded,
                ),
                "requests_cover_demanded":
                    sample.term_bit_requests >= sample.term_bits_demanded,
                "demanded_within_available":
                    sample.term_bits_demanded <= sample.term_bits_available,
                "lowering_covers_demanded":
                    sample.term_bits_lowered >= sample.term_bits_demanded,
            },
            "symbol": {
                "requests": sample.symbol_bit_requests,
                "available": sample.symbol_bits_available,
                "demanded": sample.symbol_bits_demanded,
                "lowered": sample.symbol_bits_lowered,
                "demanded_over_available": ratio_record(
                    sample.symbol_bits_demanded,
                    sample.symbol_bits_available,
                ),
                "lowered_over_demanded": ratio_record(
                    sample.symbol_bits_lowered,
                    sample.symbol_bits_demanded,
                ),
                "requests_cover_demanded":
                    sample.symbol_bit_requests >= sample.symbol_bits_demanded,
                "demanded_within_available":
                    sample.symbol_bits_demanded <= sample.symbol_bits_available,
                "lowering_covers_demanded":
                    sample.symbol_bits_lowered >= sample.symbol_bits_demanded,
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
            "construction": construction_attribution_record(&s.layer_samples),
            "bit_demand": bit_demand_attribution_record(&s.layer_samples),
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
        let sample = LayerSample::from_layers(&layers, word_preprocess, record.model_replay);
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
            "construction": {
                "cnf_subphases_are_nested_in_cnf_encode": true,
                "aig": {
                    "and_requests": layers.aig_and_requests,
                    "trivial_simplifications": layers.aig_and_trivial_simplifications,
                    "absorption_simplifications": layers.aig_and_absorption_simplifications,
                    "structural_hash_hits": layers.aig_and_structural_hash_hits,
                    "nodes_created": layers.aig_and_nodes_created,
                    "request_outcomes_partition_requests":
                        sample.aig_outcomes() == sample.aig_and_requests,
                },
                "cnf": {
                    "subphase_ms": {
                        "planning": sample.cnf_planning * 1000.0,
                        "variable_allocation": sample.cnf_variable_allocation * 1000.0,
                        "gate_encoding": sample.cnf_gate_encoding * 1000.0,
                        "root_encoding": sample.cnf_root_encoding * 1000.0,
                    },
                    "reachable_nodes": layers.cnf_reachable_nodes,
                    "skipped_helper_nodes": layers.cnf_skipped_helper_nodes,
                    "direct_root_nodes": layers.cnf_direct_root_nodes,
                    "gate_families": {
                        "xor": layers.cnf_xor_gates,
                        "not_ite": layers.cnf_not_ite_gates,
                        "not_and": layers.cnf_not_and_gates,
                        "and_tree": layers.cnf_and_tree_gates,
                        "binary_and": layers.cnf_binary_and_gates,
                    },
                    "clause_attempts": layers.cnf_clause_attempts,
                    "tautological_clauses_skipped":
                        layers.cnf_tautological_clauses_skipped,
                    "duplicate_clauses_skipped": layers.cnf_duplicate_clauses_skipped,
                    "clauses_emitted": layers.cnf_clauses,
                    "clause_outcomes_partition_attempts":
                        sample.cnf_clause_outcomes() == sample.cnf_clause_attempts,
                },
            },
            "bit_demand": instance_bit_demand_record(&sample),
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
                        summary.oracle_axeyum_only_decided += 1;
                    }
                    json!({
                        "enabled": true,
                        "backend_kind": "z3-binary",
                        "outcome": result.verdict,
                        "decision_population": if compared {
                            "both-decided"
                        } else {
                            "axeyum-only-decided"
                        },
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
                    summary.oracle_axeyum_only_decided += 1;
                    json!({
                        "enabled": true,
                        "decision_population": "axeyum-only-decided",
                        "skipped": "z3-binary-unavailable",
                    })
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
        let parsed = match read_script(file, &name, timeout, summary) {
            Ok(parsed) => parsed,
            Err(record) => return record,
        };
        let mut script = parsed.script;
        let source_hash = parsed.source_hash;
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
        let mut rewrite = apply_rewrite(&mut script, args.rewrite, &args.rewrite_disabled_rules);
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
        let configured_preprocess = if args.preprocess {
            preprocess_start.elapsed()
        } else {
            Duration::ZERO
        };
        // Charge every selected word policy to the Axeyum side of the cold
        // comparison. Before artifact v26 the canonical-only harness rewrite
        // happened before this timer and made its Axeyum/Z3 ratio omit the
        // optimization's own cost.
        let word_preprocess = rewrite.elapsed + configured_preprocess;
        let output_shape = TermStats::compute(&script.arena, &rewrite.assertions);
        let post_word_query_shape =
            QueryShapeSample::compute(&script.arena, &rewrite.assertions, &output_shape);
        summary.query_shape_files += 1;
        summary.query_shape_sample = Some(query_shape);
        summary.post_word_query_shape_sample = Some(post_word_query_shape);
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
        let end_to_end = certify_end_to_end_record(
            args,
            file,
            &source_hash,
            &script.arena,
            &script.assertions,
            primary_solve.solve.outcome,
        );
        accumulate_end_to_end(&end_to_end, &name, summary);
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
            "end_to_end_unsat": end_to_end_record(&end_to_end, args),
            "backend_stats": backend_stats_record(stats),
            "layer_attribution": instance_layer_record(&primary_solve.solve, word_preprocess),
            "dag_nodes": input_shape.dag_nodes,
            "tree_nodes": input_shape.tree_nodes,
            "max_depth": input_shape.max_depth,
            "distinct_symbols": input_shape.distinct_symbols,
            "assertions": usize_to_u64(script.assertions.len()),
            "query_shape": query_shape_record(&query_shape, &post_word_query_shape),
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
            profile_bit_demand: args.profile_bit_demand,
            demand_bit_slicing: args.demand_bit_slicing,
            range_demand_slicing: args
                .range_demand_slicing
                .then_some(args.range_demand_policy),
            ..SolverConfig::default()
        }
    }

    struct ParsedBenchmark {
        script: Script,
        source_hash: String,
    }

    fn read_script(
        file: &Path,
        name: &str,
        timeout: Duration,
        summary: &mut Summary,
    ) -> Result<ParsedBenchmark, JsonValue> {
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
                Ok(ParsedBenchmark {
                    script: s,
                    source_hash: content_hash(text.as_bytes()),
                })
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
        elapsed: Duration,
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

    fn apply_rewrite(
        script: &mut Script,
        mode: RewriteMode,
        disabled_rules: &[String],
    ) -> RewriteRun {
        match mode {
            RewriteMode::Off => RewriteRun {
                assertions: script.assertions.clone(),
                report: RewriteReport::default(),
                elapsed: Duration::ZERO,
            },
            RewriteMode::Default => {
                let start = Instant::now();
                let canonicalizer = if disabled_rules.is_empty() {
                    Canonicalizer::default()
                } else {
                    Canonicalizer::new(rewrite_ablation_manifest(disabled_rules))
                };
                let outcome = canonicalizer
                    .canonicalize_terms(&mut script.arena, &script.assertions)
                    .expect("default rewrite preserves IR well-formedness");
                RewriteRun {
                    assertions: outcome.terms,
                    report: outcome.report,
                    elapsed: start.elapsed(),
                }
            }
        }
    }

    fn rewrite_ablation_manifest(disabled_rules: &[String]) -> RewriteManifest {
        let disabled = disabled_rules
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let mut rules = default_manifest().rules().to_vec();
        for rule in &mut rules {
            if disabled.contains(rule.id.as_str()) {
                rule.enabled_by_default = false;
            }
        }
        RewriteManifest::new(rules).expect("disabling checked default rules preserves the manifest")
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

    fn certify_end_to_end_record(
        args: &Args,
        file: &Path,
        source_hash: &str,
        arena: &TermArena,
        assertions: &[TermId],
        outcome: &str,
    ) -> EndToEndRecord {
        if !args.certify_end_to_end_unsat {
            return EndToEndRecord {
                status: EndToEndStatus::NotRequested,
                elapsed: None,
                detail: None,
                hard_timeout: false,
            };
        }
        if outcome != "unsat" {
            return EndToEndRecord {
                status: EndToEndStatus::NotApplicable,
                elapsed: None,
                detail: None,
                hard_timeout: false,
            };
        }

        let deadline_ms = args
            .end_to_end_deadline_ms
            .expect("validated end-to-end certification has a deadline");
        let started = Instant::now();
        if let Some(process_timeout_ms) = args.end_to_end_process_timeout_ms {
            let isolated = certify_file_isolated(
                file,
                source_hash,
                Duration::from_millis(deadline_ms),
                Duration::from_millis(process_timeout_ms),
            );
            let status = match isolated.status {
                IsolatedStatus::Certified => EndToEndStatus::Certified,
                IsolatedStatus::NotCertified => EndToEndStatus::NotCertified,
                IsolatedStatus::SatisfiableContradiction => {
                    EndToEndStatus::SatisfiableContradiction
                }
                IsolatedStatus::RecheckFailed => EndToEndStatus::RecheckFailed,
                IsolatedStatus::Error => EndToEndStatus::Error,
            };
            return EndToEndRecord {
                status,
                elapsed: Some(started.elapsed()),
                detail: isolated.detail,
                hard_timeout: isolated.hard_timeout,
            };
        }
        let deadline = started + Duration::from_millis(deadline_ms);
        let result = certify_qf_bv_unsat_end_to_end_within(arena, assertions, Some(deadline));
        let (status, detail) = match result {
            Ok(outcome @ EndToEndUnsatOutcome::Certified { .. }) => match outcome.recheck() {
                Ok(true) => (EndToEndStatus::Certified, None),
                Ok(false) => (
                    EndToEndStatus::RecheckFailed,
                    Some(
                        "certificate text did not independently re-derive both refutations"
                            .to_owned(),
                    ),
                ),
                Err(error) => (
                    EndToEndStatus::RecheckFailed,
                    Some(format!("certificate recheck error: {error}")),
                ),
            },
            Ok(EndToEndUnsatOutcome::NotCertified) => (EndToEndStatus::NotCertified, None),
            Ok(EndToEndUnsatOutcome::Satisfiable) => (
                EndToEndStatus::SatisfiableContradiction,
                Some("end-to-end route returned satisfiable after primary UNSAT".to_owned()),
            ),
            Err(error) => (EndToEndStatus::Error, Some(error.to_string())),
        };
        EndToEndRecord {
            status,
            elapsed: Some(started.elapsed()),
            detail,
            hard_timeout: false,
        }
    }

    fn accumulate_end_to_end(record: &EndToEndRecord, path: &str, summary: &mut Summary) {
        if record.status.attempted() {
            summary.end_to_end_attempted += 1;
            let elapsed = record
                .elapsed
                .expect("attempted end-to-end certification carries elapsed time");
            summary.end_to_end_s += elapsed.as_secs_f64();
            summary.end_to_end_sample = Some(elapsed.as_secs_f64());
        }
        match record.status {
            EndToEndStatus::Certified => summary.end_to_end_certified += 1,
            EndToEndStatus::NotCertified => {
                summary.end_to_end_not_certified += 1;
                summary
                    .end_to_end_not_certified_paths
                    .insert(path.to_owned());
                if record.hard_timeout {
                    summary.end_to_end_hard_timeouts += 1;
                    summary
                        .end_to_end_hard_timeout_paths
                        .insert(path.to_owned());
                }
            }
            EndToEndStatus::SatisfiableContradiction => {
                summary.end_to_end_satisfiable_contradictions += 1;
                summary.end_to_end_alarm_paths.insert(path.to_owned());
            }
            EndToEndStatus::RecheckFailed => {
                summary.end_to_end_recheck_failures += 1;
                summary.end_to_end_alarm_paths.insert(path.to_owned());
            }
            EndToEndStatus::Error => {
                summary.end_to_end_errors += 1;
                summary.end_to_end_alarm_paths.insert(path.to_owned());
            }
            EndToEndStatus::NotRequested | EndToEndStatus::NotApplicable => {}
        }
    }

    fn end_to_end_record(record: &EndToEndRecord, args: &Args) -> JsonValue {
        json!({
            "requested": args.certify_end_to_end_unsat,
            "status": record.status.as_str(),
            "deadline_ms": args.end_to_end_deadline_ms,
            "process_timeout_ms": args.end_to_end_process_timeout_ms,
            "isolation": if args.end_to_end_process_timeout_ms.is_some() {
                "subprocess-hard-timeout"
            } else {
                "in-process-cooperative"
            },
            "hard_timeout": record.hard_timeout,
            "elapsed_ms": record.elapsed.map(duration_ms_f64),
            "detail": record.detail,
            "timing_accounting": "separate assurance work; excluded from cold solver totals",
        })
    }

    #[allow(clippy::cast_precision_loss)]
    fn end_to_end_coverage_percent(summary: &Summary) -> f64 {
        if summary.end_to_end_attempted == 0 {
            0.0
        } else {
            100.0 * summary.end_to_end_certified as f64 / summary.end_to_end_attempted as f64
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
        let sample = LayerSample::from_layers(&layers, word_preprocess, record.model_replay);
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
        total.end_to_end_attempted += next.end_to_end_attempted;
        total.end_to_end_certified += next.end_to_end_certified;
        total.end_to_end_not_certified += next.end_to_end_not_certified;
        total.end_to_end_satisfiable_contradictions += next.end_to_end_satisfiable_contradictions;
        total.end_to_end_recheck_failures += next.end_to_end_recheck_failures;
        total.end_to_end_errors += next.end_to_end_errors;
        total.end_to_end_hard_timeouts += next.end_to_end_hard_timeouts;
        total.end_to_end_s += next.end_to_end_s;
        if let Some(sample) = next.end_to_end_sample {
            total.end_to_end_samples.push(sample);
        }
        total
            .end_to_end_not_certified_paths
            .extend(next.end_to_end_not_certified_paths.iter().cloned());
        total
            .end_to_end_hard_timeout_paths
            .extend(next.end_to_end_hard_timeout_paths.iter().cloned());
        total
            .end_to_end_alarm_paths
            .extend(next.end_to_end_alarm_paths.iter().cloned());
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
        total.oracle_axeyum_only_decided += next.oracle_axeyum_only_decided;
        total.oracle_z3_only_decided += next.oracle_z3_only_decided;
        total.oracle_neither_decided += next.oracle_neither_decided;
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
        if let Some(sample) = next.post_word_query_shape_sample {
            total.post_word_query_shape_samples.push(sample);
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

    fn record_oracle_population(
        summary: &mut Summary,
        primary_decided: bool,
        oracle_decided: bool,
    ) -> &'static str {
        match (primary_decided, oracle_decided) {
            (true, true) => "both-decided",
            (true, false) => {
                summary.oracle_axeyum_only_decided += 1;
                "axeyum-only-decided"
            }
            (false, true) => {
                summary.oracle_z3_only_decided += 1;
                "z3-only-decided"
            }
            (false, false) => {
                summary.oracle_neither_decided += 1;
                "neither-decided"
            }
        }
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
        let primary_decided = matches!(primary.outcome, "sat" | "unsat");
        let mut oracle_decided = matches!(oracle_solve.outcome, "sat" | "unsat");
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
        if oracle_solve.outcome == "unsupported"
            && let Some(result) = run_z3_binary(file, config.timeout)
        {
            if let Some(verdict) = result.verdict {
                oracle_outcome = verdict;
                oracle_decided = true;
            }
            z3_binary = Some(result);
        }

        let compared = primary_decided && oracle_decided;
        let population = record_oracle_population(summary, primary_decided, oracle_decided);
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
            "decision_population": population,
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
            "summary": artifact_summary_record(args, s, instances, identity.compare_backend_name),
            "triage": artifact_triage_record(s, instances),
            "instances": instances,
        });
        serde_json::to_string_pretty(&artifact).map_err(|e| format!("render artifact: {e}"))
    }

    fn artifact_config_record(args: &Args, identity: &ArtifactIdentity<'_>) -> JsonValue {
        let manifest = identity.corpus_manifest;
        let mut record = json!({
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
            "manifest_validation_jobs": usize_to_u64(args.manifest_jobs),
            "resource_limit": optional_u64(args.resource_limit),
            "node_budget": optional_u64(args.node_budget),
            "cnf_variable_budget": optional_u64(args.cnf_variable_budget),
            "cnf_clause_budget": optional_u64(args.cnf_clause_budget),
            "cnf_inprocessing": args.cnf_inprocessing,
            "cnf_vivify": args.cnf_vivify,
            "native_cdcl": args.native_cdcl,
            "prove_unsat": args.prove_unsat,
            "certify_end_to_end_unsat": args.certify_end_to_end_unsat,
            "end_to_end_deadline_ms": args.end_to_end_deadline_ms,
            "preprocess": args.preprocess,
            "profile_bit_demand": args.profile_bit_demand,
            "demand_bit_slicing": args.demand_bit_slicing,
            "range_demand_slicing": args.range_demand_slicing,
            "range_demand_policy": args.range_demand_slicing.then(|| json!({
                "min_term_bits_available": args.range_demand_policy.min_term_bits_available,
                "min_estimated_bits_avoided": args.range_demand_policy.min_estimated_bits_avoided,
                "min_estimated_avoided_percent": args.range_demand_policy.min_estimated_avoided_percent,
                "min_exact_bits_avoided": args.range_demand_policy.min_exact_bits_avoided,
                "min_exact_avoided_percent": args.range_demand_policy.min_exact_avoided_percent,
                "analysis_work_budget": args.range_demand_policy.analysis_work_budget,
            })),
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
            "rewrite": rewrite_config(args),
            "experiment": experiment_identity_record(identity.experiment),
        });
        if let JsonValue::Object(fields) = &mut record {
            fields.insert(
                "end_to_end_process_timeout_ms".to_owned(),
                json!(args.end_to_end_process_timeout_ms),
            );
        }
        record
    }

    fn artifact_summary_record(
        args: &Args,
        s: &Summary,
        instances: &[JsonValue],
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
                    |seconds| *seconds,
                ),
                "timing_accounting": "nested within SAT solve time; not added again to cold total",
            },
            "end_to_end_unsat": {
                "requested": args.certify_end_to_end_unsat,
                "deadline_ms": args.end_to_end_deadline_ms,
                "process_timeout_ms": args.end_to_end_process_timeout_ms,
                "isolation": if args.end_to_end_process_timeout_ms.is_some() {
                    "subprocess-hard-timeout"
                } else {
                    "in-process-cooperative"
                },
                "attempted": s.end_to_end_attempted,
                "certified": s.end_to_end_certified,
                "not_certified": s.end_to_end_not_certified,
                "satisfiable_contradictions": s.end_to_end_satisfiable_contradictions,
                "recheck_failures": s.end_to_end_recheck_failures,
                "errors": s.end_to_end_errors,
                "hard_timeouts": s.end_to_end_hard_timeouts,
                "attempted_partitioned": s.end_to_end_attempted
                    == s.end_to_end_certified
                        + s.end_to_end_not_certified
                        + s.end_to_end_satisfiable_contradictions
                        + s.end_to_end_recheck_failures
                        + s.end_to_end_errors,
                "coverage_percent": end_to_end_coverage_percent(s),
                "elapsed_s": s.end_to_end_s,
                "elapsed": timing_distribution_record(
                    &s.end_to_end_samples,
                    |seconds| *seconds,
                ),
                "not_certified_paths": s.end_to_end_not_certified_paths,
                "hard_timeout_paths": s.end_to_end_hard_timeout_paths,
                "alarm_paths": s.end_to_end_alarm_paths,
                "timing_accounting": if args.end_to_end_process_timeout_ms.is_some() {
                    "separate assurance work; excluded from cold solver totals; parent hard timeout covers worker parse, construction, proof searches, and completed-proof self-recheck"
                } else {
                    "separate assurance work; excluded from cold solver totals; cooperative deadline covers proof searches, not construction or completed-proof checking"
                },
            },
            "manifest": {
                "expected": s.manifest_expected,
                "compared": s.manifest_compared,
                "agree": s.manifest_agree,
                "disagree": s.manifest_disagree,
            },
            "par2_mean_s": s.par2_seconds / decided_denominator(s),
            "blocker_buckets": s.blocker_buckets,
            "rewrite": rewrite_summary_record(s, args, instances),
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
                "decision_population": {
                    "both_decided": s.oracle_compared,
                    "axeyum_only_decided": s.oracle_axeyum_only_decided,
                    "z3_only_decided": s.oracle_z3_only_decided,
                    "neither_decided": s.oracle_neither_decided,
                    "accounted": s.oracle_compared
                        + s.oracle_axeyum_only_decided
                        + s.oracle_z3_only_decided
                        + s.oracle_neither_decided,
                },
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
                "end_to_end_satisfiable_contradictions": s.end_to_end_satisfiable_contradictions,
                "end_to_end_recheck_failures": s.end_to_end_recheck_failures,
                "end_to_end_errors": s.end_to_end_errors,
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

    fn rewrite_config(args: &Args) -> JsonValue {
        let disabled = args
            .rewrite_disabled_rules
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        let rule_ids = if args.rewrite == RewriteMode::Default {
            default_manifest()
                .enabled_rules()
                .filter(|rule| !disabled.contains(rule.id.as_str()))
                .map(|rule| rule.id.as_str().to_owned())
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        json!({
            "mode": args.rewrite.as_str(),
            "base_rule_set": if args.rewrite == RewriteMode::Default {
                JsonValue::String("axeyum-rewrite-default-v4".to_owned())
            } else {
                JsonValue::Null
            },
            "rule_set": if args.rewrite == RewriteMode::Default {
                JsonValue::String(if disabled.is_empty() {
                    "axeyum-rewrite-default-v4".to_owned()
                } else {
                    "axeyum-rewrite-default-v4-ablation".to_owned()
                })
            } else {
                JsonValue::Null
            },
            "disabled_rule_ids": disabled,
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
            "elapsed_ms": duration_ms_f64(rewrite.elapsed),
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

    #[allow(clippy::cast_precision_loss)]
    fn usize_to_f64(n: usize) -> f64 {
        usize_to_u64(n) as f64
    }

    #[allow(clippy::cast_precision_loss)]
    fn u64_to_f64(n: u64) -> f64 {
        n as f64
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
        update_hash(&mut hash, &usize_to_u64(args.manifest_jobs).to_le_bytes());
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
        for rule_id in args.rewrite_disabled_rules.iter().collect::<BTreeSet<_>>() {
            update_hash(&mut hash, rule_id.as_bytes());
            update_hash(&mut hash, &[0]);
        }
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
        update_hash(&mut hash, &[u8::from(args.cnf_vivify)]);
        update_hash(&mut hash, &[u8::from(args.native_cdcl)]);
        update_hash(&mut hash, &[u8::from(args.prove_unsat)]);
        fingerprint_end_to_end_config(&mut hash, args);
        update_hash(&mut hash, &[u8::from(args.preprocess)]);
        update_hash(&mut hash, &[u8::from(args.profile_bit_demand)]);
        update_hash(&mut hash, &[u8::from(args.demand_bit_slicing)]);
        update_hash(&mut hash, &[u8::from(args.range_demand_slicing)]);
        if args.range_demand_slicing {
            let policy = args.range_demand_policy;
            update_hash(&mut hash, &policy.min_term_bits_available.to_le_bytes());
            update_hash(&mut hash, &policy.min_estimated_bits_avoided.to_le_bytes());
            update_hash(&mut hash, &[policy.min_estimated_avoided_percent]);
            update_hash(&mut hash, &policy.min_exact_bits_avoided.to_le_bytes());
            update_hash(&mut hash, &[policy.min_exact_avoided_percent]);
            update_hash(&mut hash, &policy.analysis_work_budget.to_le_bytes());
        }
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

    fn fingerprint_end_to_end_config(hash: &mut u64, args: &Args) {
        update_hash(hash, &[u8::from(args.certify_end_to_end_unsat)]);
        update_hash(
            hash,
            &args
                .end_to_end_deadline_ms
                .unwrap_or(u64::MAX)
                .to_le_bytes(),
        );
        update_hash(
            hash,
            &args
                .end_to_end_process_timeout_ms
                .unwrap_or(u64::MAX)
                .to_le_bytes(),
        );
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
        manifest_jobs: usize,
    ) -> Result<(), String> {
        if index_path == output_path {
            return Err(
                "capture index and generated corpus manifest must use different paths".to_owned(),
            );
        }
        let index_bytes = fs::read(index_path)
            .map_err(|error| format!("read capture index {}: {error}", index_path.display()))?;
        let manifest_bytes = render_corpus_manifest_from_capture_index(
            root,
            index_path,
            &index_bytes,
            output_path,
            manifest_jobs,
        )?;
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
        manifest_jobs: usize,
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

        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(manifest_jobs)
            .build()
            .map_err(|error| format!("build manifest validation pool: {error}"))?;
        let parsed = pool.install(|| {
            file_values
                .par_iter()
                .enumerate()
                .map(|(index, value)| parse_capture_index_entry(root, index, value))
                .collect::<Vec<_>>()
        });
        let mut paths = BTreeSet::new();
        let mut entries = Vec::with_capacity(parsed.len());
        for result in parsed {
            let entry = result?;
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
        parse_corpus_manifest(root, generated_path, &rendered, None, manifest_jobs)?;
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
            args.manifest_jobs,
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
        manifest_jobs: usize,
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

        let all_entries = parse_manifest_entries(root, file_values, manifest_jobs)?;
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
        manifest_jobs: usize,
    ) -> Result<Vec<CorpusManifestEntry>, String> {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(manifest_jobs)
            .build()
            .map_err(|error| format!("build manifest validation pool: {error}"))?;
        let parsed = pool.install(|| {
            values
                .par_iter()
                .enumerate()
                .map(|(index, value)| parse_manifest_entry(root, index, value))
                .collect::<Vec<_>>()
        });
        let mut entries = Vec::with_capacity(parsed.len());
        let mut paths = BTreeSet::new();
        for result in parsed {
            let entry = result?;
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
        fn oracle_population_records_every_decided_bucket() {
            let mut summary = Summary::default();
            assert_eq!(
                record_oracle_population(&mut summary, true, true),
                "both-decided"
            );
            assert_eq!(
                record_oracle_population(&mut summary, true, false),
                "axeyum-only-decided"
            );
            assert_eq!(
                record_oracle_population(&mut summary, false, true),
                "z3-only-decided"
            );
            assert_eq!(
                record_oracle_population(&mut summary, false, false),
                "neither-decided"
            );
            assert_eq!(summary.oracle_axeyum_only_decided, 1);
            assert_eq!(summary.oracle_z3_only_decided, 1);
            assert_eq!(summary.oracle_neither_decided, 1);
        }

        #[test]
        fn incremental_batch_backend_uses_the_public_cold_embedding_path() {
            assert_eq!(
                parse_backend("incremental-bv-batch").unwrap(),
                BackendKind::IncrementalBvBatch
            );
            let mut arena = TermArena::new();
            let x = arena.bv_var("x", 8).unwrap();
            let one = arena.bv_const(8, 1).unwrap();
            let five = arena.bv_const(8, 5).unwrap();
            let six = arena.bv_const(8, 6).unwrap();
            let sum = arena.bv_add(x, one).unwrap();
            let assertions = [arena.eq(sum, five).unwrap(), arena.eq(x, six).unwrap()];
            let mut backend = IncrementalBvBatchBackend::new();

            assert!(matches!(
                backend.check(&arena, &assertions, &SolverConfig::default()),
                Ok(CheckResult::Unsat)
            ));
            let stats = backend.last_stats().unwrap();
            assert_eq!(stats.assertion_count, 2);
            assert!(
                stats
                    .backend
                    .iter()
                    .any(|(name, value)| { name == "incremental_cnf_clauses" && *value > 0.0 })
            );
        }

        #[test]
        fn incremental_raw_profile_backend_exposes_gate_mix_without_reusing_batch_policy() {
            assert_eq!(
                parse_backend("incremental-bv-raw-profile").unwrap(),
                BackendKind::IncrementalBvRawProfile
            );
            let mut arena = TermArena::new();
            let a = arena.bool_var("a").unwrap();
            let b = arena.bool_var("b").unwrap();
            let assertion = arena.and(a, b).unwrap();
            let mut backend = IncrementalBvRawProfileBackend::new();

            assert!(matches!(
                backend.check(&arena, &[assertion], &SolverConfig::default()),
                Ok(CheckResult::Sat(_))
            ));
            let stats = backend.last_stats().unwrap();
            let value = |name: &str| {
                stats
                    .backend
                    .iter()
                    .find_map(|(candidate, value)| (candidate == name).then_some(*value))
                    .unwrap()
            };
            assert!(value("incremental_cnf_and_nodes_synced") > 0.0);
            assert!(value("incremental_cnf_definition_clauses").abs() < f64::EPSILON);
            assert!((value("incremental_cnf_root_clauses") - 2.0).abs() < f64::EPSILON);
            assert!(
                (value("incremental_cnf_direct_positive_and_roots") - 1.0).abs() < f64::EPSILON
            );
            assert!((value("incremental_cnf_fused_positive_and_roots") - 1.0).abs() < f64::EPSILON);
            assert!((value("incremental_cnf_fused_positive_and_nodes") - 1.0).abs() < f64::EPSILON);
            assert!((value("incremental_cnf_root_assertions") - 1.0).abs() < f64::EPSILON);
            assert!(value("incremental_cnf_guarded_root_assertions").abs() < f64::EPSILON);
            assert!(value("incremental_cnf_duplicate_root_clauses").abs() < f64::EPSILON);
            assert!(value("incremental_cnf_duplicate_prior_root_clauses").abs() < f64::EPSILON);
            assert!(value("incremental_cnf_root_clauses_duplicate_non_root").abs() < f64::EPSILON);
            assert!(value("incremental_cnf_deduplicated_root_assertions").abs() < f64::EPSILON);
            assert!((value("incremental_cnf_root_clause_attempts") - 2.0).abs() < f64::EPSILON);
            assert!(
                (value("incremental_cnf_unit_payload_root_clauses") - 2.0).abs() < f64::EPSILON
            );
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
                report_summary(&mostly_failed, None, false, false),
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
                report_summary(&incomplete, Some(80.0), false, false),
                ExitCode::SUCCESS
            );
            assert_eq!(
                report_summary(&incomplete, Some(80.1), false, false),
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
                report_summary(&complete, Some(100.0), true, false),
                ExitCode::SUCCESS
            );

            let partial = Summary {
                client_comparison_files: 1,
                ..complete
            };
            assert_eq!(
                report_summary(&partial, Some(100.0), true, false),
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
                2,
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
                1,
            )
            .unwrap();
            let second = render_corpus_manifest_from_capture_index(
                &micro_corpus_root(),
                Path::new("capture-index.json"),
                &index,
                Path::new("generated-manifest.json"),
                3,
            )
            .unwrap();
            assert_eq!(first, second);
            assert_eq!(first.last(), Some(&b'\n'));

            let selection = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("generated-manifest.json"),
                &first,
                Some("representative"),
                2,
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
                2,
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
                2,
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
                2,
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
                2,
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
                2,
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
                2,
            )
            .unwrap_err();
            assert!(error.contains("duplicate corpus manifest path"), "{error}");

            let error = parse_corpus_manifest(
                &micro_corpus_root(),
                Path::new("micro-manifest.json"),
                &serde_json::to_vec(&micro_manifest_value()).unwrap(),
                Some("nightly"),
                2,
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
                report_summary(&summary, Some(100.0), false, false),
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
                    ..LayerSample::default()
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
                    ..LayerSample::default()
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
        fn construction_attribution_partitions_requests_and_clause_attempts() {
            let samples = [
                LayerSample {
                    aig_and_requests: 10,
                    aig_and_trivial_simplifications: 1,
                    aig_and_absorption_simplifications: 2,
                    aig_and_structural_hash_hits: 3,
                    aig_and_nodes_created: 4,
                    cnf_clauses: 32,
                    cnf_planning: 0.0001,
                    cnf_clause_attempts: 35,
                    cnf_tautological_clauses_skipped: 1,
                    cnf_duplicate_clauses_skipped: 2,
                    ..LayerSample::default()
                },
                LayerSample {
                    aig_and_requests: 100,
                    aig_and_trivial_simplifications: 10,
                    aig_and_absorption_simplifications: 20,
                    aig_and_structural_hash_hits: 30,
                    aig_and_nodes_created: 40,
                    cnf_clauses: 320,
                    cnf_planning: 0.001,
                    cnf_clause_attempts: 325,
                    cnf_tautological_clauses_skipped: 2,
                    cnf_duplicate_clauses_skipped: 3,
                    ..LayerSample::default()
                },
            ];
            let record = construction_attribution_record(&samples);
            assert_eq!(record["aig"]["and_requests"], json!(110));
            assert_eq!(
                record["aig"]["request_outcomes_partition_requests"],
                json!(true)
            );
            assert_eq!(
                record["cnf"]["subphase_distributions"]["planning"]["p95_ms"],
                json!(1.0)
            );
            assert_eq!(record["cnf"]["clause_attempts"], json!(360));
            assert_eq!(
                record["cnf"]["clause_outcomes_partition_attempts"],
                json!(true)
            );
        }

        #[test]
        fn bit_demand_attribution_exposes_current_over_lowering() {
            let samples = [LayerSample {
                bit_demand_analysis: 0.0005,
                bit_demand_profile_complete: true,
                term_bit_requests: 25,
                term_bits_available: 81,
                term_bits_demanded: 25,
                term_bits_lowered: 81,
                symbol_bit_requests: 8,
                symbol_bits_available: 64,
                symbol_bits_demanded: 8,
                symbol_bits_lowered: 64,
                ..LayerSample::default()
            }];
            let record = bit_demand_attribution_record(&samples);
            assert_eq!(record["profile_mode"], json!("structural-observational"));
            assert_eq!(record["lowering_applied"], json!(false));
            assert_eq!(record["analysis_distribution"]["p50_ms"], json!(0.5));
            assert_eq!(
                record["term"]["demanded_over_available"],
                json!(25.0 / 81.0)
            );
            assert_eq!(record["term"]["lowered_over_demanded"], json!(81.0 / 25.0));
            assert_eq!(record["term"]["lowering_covers_demanded"], json!(true));
            assert_eq!(record["symbol"]["demanded_over_available"], json!(0.125));
            assert_eq!(record["symbol"]["lowered_over_demanded"], json!(8.0));
        }

        #[test]
        fn bit_demand_attribution_distinguishes_production_slicing() {
            let samples = [LayerSample {
                bit_demand_profile_complete: true,
                bit_demand_lowering_applied: true,
                term_bit_requests: 25,
                term_bits_available: 81,
                term_bits_demanded: 25,
                term_bits_lowered: 25,
                symbol_bit_requests: 8,
                symbol_bits_available: 64,
                symbol_bits_demanded: 8,
                symbol_bits_lowered: 8,
                ..LayerSample::default()
            }];
            let corpus = bit_demand_attribution_record(&samples);
            let instance = instance_bit_demand_record(&samples[0]);
            assert_eq!(corpus["profile_mode"], json!("structural-lowering"));
            assert_eq!(corpus["lowering_applied"], json!(true));
            assert_eq!(corpus["lowering_applied_samples"], json!(1));
            assert_eq!(corpus["term"]["lowered_over_demanded"], json!(1.0));
            assert_eq!(instance["profile_mode"], json!("structural-lowering"));
            assert_eq!(instance["lowering_applied"], json!(true));
        }

        #[test]
        fn range_demand_attribution_partitions_admission_and_work() {
            let samples = [
                LayerSample {
                    bit_demand_profile_complete: true,
                    bit_demand_lowering_applied: true,
                    range_demand_decision: RangeDemandDecision::Applied,
                    range_demand_admission: 0.000_2,
                    range_demand_estimated_bits_avoided: 56,
                    range_demand_analysis_work_budget: 1_000,
                    range_demand_analysis_work: 17,
                    range_demand_merges: 2,
                    ..LayerSample::default()
                },
                LayerSample {
                    bit_demand_profile_complete: true,
                    range_demand_decision: RangeDemandDecision::NoCandidate,
                    range_demand_admission: 0.000_1,
                    ..LayerSample::default()
                },
            ];
            let corpus = bit_demand_attribution_record(&samples);
            assert_eq!(corpus["range"]["decision_counts"]["applied"], json!(1));
            assert_eq!(corpus["range"]["decision_counts"]["no-candidate"], json!(1));
            assert_eq!(corpus["range"]["estimated_bits_avoided"], json!(56));
            assert_eq!(corpus["range"]["analysis_work"], json!(17));
            assert_eq!(corpus["range"]["analysis_work_within_budget"], json!(true));
            assert_eq!(corpus["range"]["range_merges"], json!(2));

            let instance = instance_bit_demand_record(&samples[0]);
            assert_eq!(instance["range"]["decision"], json!("applied"));
            assert_eq!(instance["range"]["admission_ms"], json!(0.2));
        }

        #[test]
        fn unprofiled_bit_demand_is_explicitly_unavailable() {
            let sample = LayerSample {
                term_bits_lowered: 81,
                symbol_bits_lowered: 64,
                ..LayerSample::default()
            };
            let corpus = bit_demand_attribution_record(&[sample]);
            assert_eq!(corpus["profile_complete"], json!(false));
            assert_eq!(corpus["profile_mode"], json!("off"));
            assert!(corpus["term"]["demanded"].is_null());
            assert_eq!(corpus["term"]["lowered"], json!(81));
            assert!(corpus["term"]["lowering_covers_demanded"].is_null());

            let instance = instance_bit_demand_record(&sample);
            assert_eq!(instance["profile_complete"], json!(false));
            assert!(instance["symbol"]["available"].is_null());
            assert_eq!(instance["symbol"]["lowered"], json!(64));
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
            assert_eq!(
                report_summary(&missing, None, false, false),
                ExitCode::FAILURE
            );

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
        fn end_to_end_accounting_keeps_uncovered_rows_and_fails_on_alarms() {
            let certified = EndToEndRecord {
                status: EndToEndStatus::Certified,
                elapsed: Some(Duration::from_millis(2)),
                detail: None,
                hard_timeout: false,
            };
            let uncovered = EndToEndRecord {
                status: EndToEndStatus::NotCertified,
                elapsed: Some(Duration::from_millis(5)),
                detail: Some("worker killed and reaped".to_owned()),
                hard_timeout: true,
            };
            let mut summary = Summary {
                unsat: 2,
                ..Summary::default()
            };
            accumulate_end_to_end(&certified, "a.smt2", &mut summary);
            accumulate_end_to_end(&uncovered, "b.smt2", &mut summary);
            assert_eq!(summary.end_to_end_attempted, 2);
            assert_eq!(summary.end_to_end_certified, 1);
            assert_eq!(summary.end_to_end_not_certified, 1);
            assert_eq!(summary.end_to_end_hard_timeouts, 1);
            assert!(summary.end_to_end_not_certified_paths.contains("b.smt2"));
            assert!(summary.end_to_end_hard_timeout_paths.contains("b.smt2"));
            assert!((end_to_end_coverage_percent(&summary) - 50.0).abs() < f64::EPSILON);
            assert_eq!(
                report_summary(&summary, None, false, true),
                ExitCode::SUCCESS
            );

            let alarm = EndToEndRecord {
                status: EndToEndStatus::SatisfiableContradiction,
                elapsed: Some(Duration::from_millis(1)),
                detail: Some("contradiction".to_owned()),
                hard_timeout: false,
            };
            summary.unsat += 1;
            accumulate_end_to_end(&alarm, "c.smt2", &mut summary);
            assert_eq!(
                report_summary(&summary, None, false, true),
                ExitCode::FAILURE
            );
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
            assert_eq!(shape.low_extract_over_sign_ext, 1);
            assert_eq!(shape.extract_concat_straddling, 1);
            assert_eq!(shape.extract_concat_low_side, 0);
            assert_eq!(shape.extract_concat_high_side, 0);
            assert_eq!(shape.extract_zero_ext_low_region, 1);
            assert_eq!(shape.extract_sign_ext_low_region, 1);
            assert_eq!(shape.max_nested_extract_depth, 1);
            assert_eq!(shape.cancellation_opportunities(), 4);
            assert_eq!((shape.selects, shape.stores), (1, 1));
            assert!(shape.distinct_bitvec_widths >= 3);

            let summary = Summary {
                query_shape_files: 1,
                query_shape_samples: vec![shape],
                post_word_query_shape_samples: vec![shape],
                ..Summary::default()
            };
            let record = query_shape_summary_record(&summary);
            assert_eq!(
                record["coercion_cancellation_opportunities"]["total"],
                json!(4)
            );
            assert_eq!(
                record["coercion_cancellation_opportunities"]["concat_regions"]["straddling"],
                json!(1)
            );
            assert_eq!(
                record["opportunity_transition"]["total"]["removed"],
                json!(0)
            );
            assert_eq!(record["post_word_profile_complete"], json!(true));
            assert_eq!(
                record["memory_provenance"]["surviving_select_store_ops"],
                json!(2)
            );
            assert_eq!(
                record["formula_distributions"]["dag_nodes"]["p50"],
                json!(shape.dag_nodes)
            );
            assert_eq!(
                record["qfbv_operator_totals"]["bit_vector"]["structural"]["extract"],
                json!(shape.extracts)
            );
            assert_eq!(
                record["qfbv_operator_totals"]["other"],
                json!(shape.selects + shape.stores)
            );
        }

        #[test]
        fn qfbv_operator_inventory_classifies_every_scalar_operator() {
            let operators = [
                Op::BoolNot,
                Op::BoolAnd,
                Op::BoolOr,
                Op::BoolXor,
                Op::BoolImplies,
                Op::BvNot,
                Op::BvAnd,
                Op::BvOr,
                Op::BvXor,
                Op::BvNand,
                Op::BvNor,
                Op::BvXnor,
                Op::BvNeg,
                Op::BvAdd,
                Op::BvSub,
                Op::BvMul,
                Op::BvUdiv,
                Op::BvUrem,
                Op::BvSdiv,
                Op::BvSrem,
                Op::BvSmod,
                Op::BvShl,
                Op::BvLshr,
                Op::BvAshr,
                Op::BvUlt,
                Op::BvUle,
                Op::BvUgt,
                Op::BvUge,
                Op::BvSlt,
                Op::BvSle,
                Op::BvSgt,
                Op::BvSge,
                Op::Eq,
                Op::Ite,
                Op::BvComp,
                Op::Extract { hi: 7, lo: 0 },
                Op::Concat,
                Op::ZeroExt { by: 8 },
                Op::SignExt { by: 8 },
                Op::RotateLeft { by: 1 },
                Op::RotateRight { by: 1 },
            ];
            let mut counts = QfBvOperatorCounts::default();
            for op in operators {
                counts.record(op);
            }
            assert_eq!(counts.applications(), usize_to_u64(operators.len()));
            assert_eq!(counts.other, 0);

            counts.record(Op::Select);
            let record = qfbv_operator_record(&counts);
            assert_eq!(record["applications"], json!(operators.len() + 1));
            assert_eq!(record["bit_vector"]["arithmetic"]["add"], json!(1));
            assert_eq!(record["bit_vector"]["comparisons"]["sge"], json!(1));
            assert_eq!(record["polymorphic"]["ite"], json!(1));
            assert_eq!(record["other"], json!(1));
        }

        #[test]
        fn query_shape_classifies_concat_extension_regions_and_nested_depth() {
            let text = "\
                (set-logic QF_BV)\n\
                (declare-const x (_ BitVec 8))\n\
                (declare-const y (_ BitVec 8))\n\
                (assert (= ((_ extract 7 0) (concat x y)) ((_ extract 7 0) (concat x y))))\n\
                (assert (= ((_ extract 15 8) (concat x y)) ((_ extract 15 8) (concat x y))))\n\
                (assert (= ((_ extract 10 6) (concat x y)) ((_ extract 10 6) (concat x y))))\n\
                (assert (= ((_ extract 7 0) ((_ zero_extend 8) x)) ((_ extract 7 0) ((_ zero_extend 8) x))))\n\
                (assert (= ((_ extract 15 8) ((_ zero_extend 8) x)) ((_ extract 15 8) ((_ zero_extend 8) x))))\n\
                (assert (= ((_ extract 10 6) ((_ zero_extend 8) x)) ((_ extract 10 6) ((_ zero_extend 8) x))))\n\
                (assert (= ((_ extract 7 0) ((_ sign_extend 8) x)) ((_ extract 7 0) ((_ sign_extend 8) x))))\n\
                (assert (= ((_ extract 15 8) ((_ sign_extend 8) x)) ((_ extract 15 8) ((_ sign_extend 8) x))))\n\
                (assert (= ((_ extract 10 6) ((_ sign_extend 8) x)) ((_ extract 10 6) ((_ sign_extend 8) x))))\n\
                (assert (= ((_ extract 3 0) ((_ extract 5 0) ((_ extract 7 0) x)))\n\
                           ((_ extract 3 0) ((_ extract 5 0) ((_ extract 7 0) x)))))\n\
                (check-sat)\n";
            let script = parse_script(text).expect("region fixture parses");
            let stats = TermStats::compute(&script.arena, &script.assertions);
            let shape = QueryShapeSample::compute(&script.arena, &script.assertions, &stats);

            assert_eq!(shape.extract_over_concat, 3);
            assert_eq!(shape.extract_concat_low_side, 1);
            assert_eq!(shape.extract_concat_high_side, 1);
            assert_eq!(shape.extract_concat_straddling, 1);
            assert_eq!(shape.extract_concat_whole_low, 1);
            assert_eq!(shape.extract_concat_whole_high, 1);

            assert_eq!(shape.extract_over_zero_ext, 3);
            assert_eq!(shape.extract_zero_ext_low_region, 1);
            assert_eq!(shape.extract_zero_ext_high_region, 1);
            assert_eq!(shape.extract_zero_ext_straddling, 1);
            assert_eq!(shape.low_extract_over_zero_ext, 1);

            assert_eq!(shape.extract_over_sign_ext, 3);
            assert_eq!(shape.extract_sign_ext_low_region, 1);
            assert_eq!(shape.extract_sign_ext_high_region, 1);
            assert_eq!(shape.extract_sign_ext_straddling, 1);
            assert_eq!(shape.low_extract_over_sign_ext, 1);

            assert_eq!(shape.extract_over_extract, 2);
            assert_eq!(shape.max_nested_extract_depth, 2);
        }

        #[test]
        fn query_shape_reports_opportunities_removed_by_the_selected_word_policy() {
            let text = "\
                (set-logic QF_BV)\n\
                (declare-const x (_ BitVec 8))\n\
                (declare-const y (_ BitVec 8))\n\
                (assert (= ((_ extract 7 0) (concat x y)) y))\n\
                (check-sat)\n";
            let mut script = parse_script(text).expect("transition fixture parses");
            let before_stats = TermStats::compute(&script.arena, &script.assertions);
            let before =
                QueryShapeSample::compute(&script.arena, &script.assertions, &before_stats);
            assert_eq!(before.extract_concat_low_side, 1);
            assert_eq!(before.extract_concat_whole_low, 1);

            let rewrite = apply_rewrite(&mut script, RewriteMode::Default, &[]);
            let after_stats = TermStats::compute(&script.arena, &rewrite.assertions);
            let after = QueryShapeSample::compute(&script.arena, &rewrite.assertions, &after_stats);
            let record = query_shape_record(&before, &after);
            assert_eq!(
                record["opportunity_transition"]["extract_over_concat"]["before"],
                json!(1)
            );
            assert_eq!(
                record["opportunity_transition"]["extract_over_concat"]["after"],
                json!(0)
            );
            assert_eq!(
                record["opportunity_transition"]["concat_regions"]["whole_low_operand"]["removed"],
                json!(1)
            );
            assert!(
                record["post_word_policy"]["formula"]["dag_nodes"]
                    .as_u64()
                    .unwrap()
                    < record["formula"]["dag_nodes"].as_u64().unwrap()
            );
        }

        #[test]
        fn rewrite_ablation_disables_only_the_named_default_rule() {
            let text = "\
                (set-logic QF_BV)\n\
                (declare-const x (_ BitVec 16))\n\
                (assert (= ((_ extract 3 0) ((_ extract 7 0) x)) #x0))\n\
                (check-sat)\n";
            let mut baseline = parse_script(text).unwrap();
            let baseline = apply_rewrite(&mut baseline, RewriteMode::Default, &[]);
            assert!(
                baseline
                    .report
                    .applications()
                    .iter()
                    .any(|application| { application.rule_id.as_str() == "bv.extract_nested.v1" })
            );

            let mut ablated = parse_script(text).unwrap();
            let ablated = apply_rewrite(
                &mut ablated,
                RewriteMode::Default,
                &["bv.extract_nested.v1".to_owned()],
            );
            assert!(
                ablated
                    .report
                    .applications()
                    .iter()
                    .all(|application| { application.rule_id.as_str() != "bv.extract_nested.v1" })
            );
            let manifest = rewrite_ablation_manifest(&["bv.extract_nested.v1".to_owned()]);
            let enabled = manifest
                .enabled_rules()
                .map(|rule| rule.id.as_str())
                .collect::<BTreeSet<_>>();
            assert!(!enabled.contains("bv.extract_nested.v1"));
            assert!(enabled.contains("bv.extract_concat.v1"));
        }

        #[test]
        fn rewrite_rule_attribution_counts_instances_and_families_without_claiming_savings() {
            let instances = vec![
                json!({
                    "cold_total_ms": 2.5,
                    "corpus_manifest": {"family": "register-slice"},
                    "rewrite": {
                        "rule_counts": {"bv.extract_nested.v1": 3},
                        "input_dag_nodes": 100,
                        "output_dag_nodes": 80,
                        "input_tree_nodes": 200,
                        "output_tree_nodes": 150,
                    },
                    "layer_attribution": {
                        "aig_nodes": 40,
                        "cnf_variables": 20,
                        "cnf_clauses": 60,
                    },
                }),
                json!({
                    "cold_total_ms": 1.5,
                    "corpus_manifest": {"family": "slice-partial"},
                    "rewrite": {
                        "rule_counts": {
                            "bv.extract_nested.v1": 1,
                            "bv.extract_extend.v1": 2,
                        },
                        "input_dag_nodes": 50,
                        "output_dag_nodes": 45,
                        "input_tree_nodes": 70,
                        "output_tree_nodes": 60,
                    },
                    "layer_attribution": {
                        "aig_nodes": 10,
                        "cnf_variables": 8,
                        "cnf_clauses": 12,
                    },
                }),
            ];
            let record = rewrite_rule_attribution_record(&instances);
            let nested = &record["rules"]["bv.extract_nested.v1"];
            assert_eq!(nested["applications"], json!(4));
            assert_eq!(nested["affected_instances"], json!(2));
            assert_eq!(nested["affected_families"]["register-slice"], json!(1));
            assert_eq!(nested["affected_families"]["slice-partial"], json!(1));
            assert_eq!(nested["dag_nodes_removed"], json!(25));
            assert_eq!(nested["selected_policy_output"]["aig_nodes"], json!(50));
            assert_eq!(nested["selected_policy_output"]["cnf_clauses"], json!(72));
            assert_eq!(
                record["selected_policy_output_is_not_saved_work"],
                json!(true)
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
                ..LayerSample::default()
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
                post_word_query_shape_sample: Some(QueryShapeSample {
                    dag_nodes: 24,
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
            assert_eq!(total.post_word_query_shape_samples.len(), 1);
            assert_eq!(total.post_word_query_shape_samples[0].dag_nodes, 24);
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
