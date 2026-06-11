//! Benchmark harness (benchmarking-and-performance-methodology note).
//!
//! Walks a corpus directory of `.smt2` files, runs each through the solver
//! trait, and emits a versioned JSON results artifact: per-instance result,
//! ground-truth agreement, layer-attributed timing, and PAR-2 scoring.
//! Disagreement with a benchmark's `:status` is a soundness alarm and makes
//! the run exit nonzero.
//!
//! Usage: `axeyum-bench <dir> [--timeout-ms N] [--limit N] [--out FILE]`
//! Build with `--features z3` (or `z3-static`).

fn main() -> std::process::ExitCode {
    run::main()
}

#[cfg(not(feature = "z3"))]
mod run {
    //! Stub when no backend feature is enabled.
    pub fn main() -> std::process::ExitCode {
        eprintln!("axeyum-bench requires a backend: build with --features z3 (or z3-static)");
        std::process::ExitCode::FAILURE
    }
}

#[cfg(feature = "z3")]
mod run {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::ExitCode;
    use std::time::Duration;

    use axeyum_ir::{TermStats, Value, eval};
    use axeyum_smtlib::{Script, SmtError, parse_script};
    use axeyum_solver::{CheckResult, Model, SolverBackend, SolverConfig, Z3Backend};
    use serde_json::{Value as JsonValue, json};

    const ARTIFACT_VERSION: u32 = 1;
    const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

    struct Args {
        dir: PathBuf,
        timeout_ms: u64,
        limit: usize,
        out: Option<PathBuf>,
    }

    fn parse_args() -> Result<Args, String> {
        let mut args = std::env::args().skip(1);
        let dir = PathBuf::from(args.next().ok_or("usage: axeyum-bench <dir> [options]")?);
        let mut parsed = Args {
            dir,
            timeout_ms: 5000,
            limit: usize::MAX,
            out: None,
        };
        while let Some(flag) = args.next() {
            let mut value = || args.next().ok_or(format!("missing value for {flag}"));
            match flag.as_str() {
                "--timeout-ms" => {
                    parsed.timeout_ms = value()?.parse().map_err(|e| format!("{e}"))?;
                }
                "--limit" => parsed.limit = value()?.parse().map_err(|e| format!("{e}"))?,
                "--out" => parsed.out = Some(PathBuf::from(value()?)),
                other => return Err(format!("unknown flag `{other}`")),
            }
        }
        Ok(parsed)
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
        par2_seconds: f64,
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
        let mut backend = Z3Backend::new();
        let backend_name = backend.capabilities().name;
        let corpus_hash = fingerprint_corpus(&files, &args.dir);
        let config_hash = fingerprint_config(&args, &backend_name, &corpus_hash);

        for file in &files {
            summary.files += 1;
            instances.push(run_one(&mut backend, file, timeout, &mut summary));
        }

        let artifact = match render_artifact(
            &args,
            &summary,
            &instances,
            &backend_name,
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
             agree={} DISAGREE={} model_replay_failures={} par2_mean_s={:.3}",
            summary.files,
            summary.sat,
            summary.unsat,
            summary.unknown,
            summary.unsupported,
            summary.errors,
            summary.agree,
            summary.disagree,
            summary.model_replay_failures,
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
        ExitCode::SUCCESS
    }

    fn decided_denominator(s: &Summary) -> f64 {
        #[allow(clippy::cast_precision_loss)]
        let n = (s.sat + s.unsat + s.unknown + s.errors).max(1) as f64;
        n
    }

    /// Runs one instance and returns its JSON record.
    fn run_one(
        backend: &mut Z3Backend,
        file: &Path,
        timeout: Duration,
        summary: &mut Summary,
    ) -> JsonValue {
        let name = file.display().to_string();
        let script = match read_script(file, &name, timeout, summary) {
            Ok(script) => script,
            Err(record) => return record,
        };
        let shape = TermStats::compute(&script.arena, &script.assertions);
        let config = SolverConfig {
            timeout: Some(timeout),
            ..SolverConfig::default()
        };
        let result = backend.check(&script.arena, &script.assertions, &config);
        let (outcome, detail) = classify_result(result, &script, summary);
        // PAR-2: solved instances score wall time; everything else 2x timeout.
        let stats = backend.last_stats().cloned().unwrap_or_default();
        let wall = stats.translate.as_secs_f64()
            + stats.solve.as_secs_f64()
            + stats.model_lift.as_secs_f64();
        if matches!(outcome, "sat" | "unsat") {
            summary.par2_seconds += wall;
        } else {
            summary.par2_seconds += 2.0 * timeout.as_secs_f64();
        }
        // Ground-truth agreement.
        if let (Some(expected @ ("sat" | "unsat")), got @ ("sat" | "unsat")) =
            (script.status.as_deref(), outcome)
        {
            if expected == got {
                summary.agree += 1;
            } else {
                summary.disagree += 1;
            }
        }
        let mut record = json!({
            "file": name,
            "outcome": outcome,
            "expected": script.status.as_deref().unwrap_or("unknown"),
            "translate_ms": duration_ms(stats.translate),
            "solve_ms": duration_ms(stats.solve),
            "model_lift_ms": duration_ms(stats.model_lift),
            "dag_nodes": shape.dag_nodes,
            "tree_nodes": shape.tree_nodes,
            "max_depth": shape.max_depth,
            "distinct_symbols": shape.distinct_symbols,
            "assertions": usize_to_u64(script.assertions.len()),
        });
        if let Some(detail) = detail
            && let JsonValue::Object(obj) = &mut record
        {
            obj.insert("detail".to_owned(), json!(detail));
        }
        record
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

    fn classify_result(
        result: Result<CheckResult, axeyum_solver::SolverError>,
        script: &Script,
        summary: &mut Summary,
    ) -> (&'static str, Option<String>) {
        match result {
            Ok(CheckResult::Sat(model)) => {
                match replay_model(&script.arena, &script.assertions, &model) {
                    Ok(()) => {
                        summary.sat += 1;
                        ("sat", None)
                    }
                    Err(e) => {
                        summary.errors += 1;
                        summary.model_replay_failures += 1;
                        ("model-replay-error", Some(e))
                    }
                }
            }
            Ok(CheckResult::Unsat) => {
                summary.unsat += 1;
                ("unsat", None)
            }
            Ok(CheckResult::Unknown(r)) => {
                summary.unknown += 1;
                ("unknown", Some(format!("{:?}: {}", r.kind, r.detail)))
            }
            Err(e) => {
                summary.errors += 1;
                ("solver-error", Some(e.to_string()))
            }
        }
    }

    fn replay_model(
        arena: &axeyum_ir::TermArena,
        assertions: &[axeyum_ir::TermId],
        model: &Model,
    ) -> Result<(), String> {
        let assignment = model.to_assignment();
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
        corpus_hash: &str,
        config_hash: &str,
    ) -> Result<String, String> {
        let limit = if args.limit == usize::MAX {
            JsonValue::Null
        } else {
            json!(usize_to_u64(args.limit))
        };
        let artifact = json!({
            "version": ARTIFACT_VERSION,
            "config": {
                "corpus": args.dir.display().to_string(),
                "corpus_hash": corpus_hash,
                "config_hash": config_hash,
                "timeout_ms": args.timeout_ms,
                "limit": limit,
                "backend": backend_name,
                "harness": format!("axeyum-bench {}", env!("CARGO_PKG_VERSION")),
                "seed": "none",
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
            },
            "instances": instances,
        });
        serde_json::to_string_pretty(&artifact).map_err(|e| format!("render artifact: {e}"))
    }

    fn duration_ms(duration: Duration) -> u64 {
        u64::try_from(duration.as_millis()).unwrap_or(u64::MAX)
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
        update_hash(&mut hash, &usize_to_u64(args.limit).to_le_bytes());
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
}
