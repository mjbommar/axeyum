//! Per-division ablation of unconstrained-variable elimination.
//!
//! Nobody has published a pass-level ablation for a modern SMT preprocessor, so
//! this walks a corpus directory and, for every `.smt2` under it, runs the
//! word-level prefix the solver actually runs (`canonicalize` →
//! `propagate_values` → `solve_eqs`) and then measures **three** configurations
//! of `elim_unconstrained` on the identical input:
//!
//! | arm | registry |
//! |---|---|
//! | `off` | empty — the pass is a no-op |
//! | `legacy` | the six bit-vector operators the pass covered before the widening |
//! | `wide` | the shipped registry (core + bit-vector + arithmetic) |
//!
//! The `legacy` arm is built here rather than in the library: it wraps the real
//! plugins and discards any inversion whose rule name is outside the historical
//! six, so it reproduces the old behaviour through the new code path and the
//! only difference measured is the RULE SET.
//!
//! For each arm it reports DAG nodes after the pass, layers eliminated and wall
//! time, aggregated per division (the corpus directory's `QF_*` path component).
//! The published cross-solver figure to compare against is Jonáš & Strejček's
//! **0.03 s average** simplification cost (SAT 2017).
//!
//! ```sh
//! cargo run --release -p axeyum-bench --example elim_unconstrained_ablation -- <dir>…
//! ```
#![allow(clippy::doc_markdown)]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

use axeyum_ir::{IrError, Op, Sort, TermArena, TermId, TermStats};
use axeyum_rewrite::{
    BvInverter, DEFAULT_SOLVE_EQS_FUEL, Inversion, Inverter, InverterCtx, InverterRegistry, Theory,
    canonicalize_terms, elim_unconstrained_with, propagate_values, solve_eqs_bounded,
};
use axeyum_smtlib::parse_script;

/// The six rule names the pass covered before the widening.
const LEGACY_RULES: [&str; 6] = [
    "bv/not",
    "bv/neg",
    "bv/add",
    "bv/xor",
    "bv/sub",
    "bv/mul-odd-const",
];

/// Wraps a real plugin and drops any inversion outside `allowed`, so an
/// historical rule set can be replayed through the current code path.
#[derive(Debug)]
struct RuleFilter {
    inner: Box<dyn Inverter>,
    allowed: &'static [&'static str],
}

impl Inverter for RuleFilter {
    fn theory(&self) -> Theory {
        self.inner.theory()
    }

    fn invert(
        &self,
        ctx: &mut InverterCtx<'_>,
        op: Op,
        args: &[TermId],
        idx: usize,
        result_sort: Sort,
    ) -> Result<Option<Inversion>, IrError> {
        let inversion = self.inner.invert(ctx, op, args, idx, result_sort)?;
        Ok(inversion.filter(|i| self.allowed.contains(&i.rule)))
    }
}

fn legacy_registry() -> InverterRegistry {
    let mut registry = InverterRegistry::new();
    registry.register(Box::new(RuleFilter {
        inner: Box::new(BvInverter),
        allowed: &LEGACY_RULES,
    }));
    registry
}

#[derive(Debug, Default, Clone)]
struct ArmTotals {
    nodes_after: u64,
    eliminated: u64,
    micros: u64,
    files_with_firing: u64,
    max_micros: u64,
    rules: BTreeMap<String, u64>,
}

#[derive(Debug, Default, Clone)]
struct DivisionTotals {
    files: u64,
    parsed: u64,
    nodes_before: u64,
    off: ArmTotals,
    legacy: ArmTotals,
    wide: ArmTotals,
}

fn division_of(path: &Path) -> String {
    for component in path.components() {
        let name = component.as_os_str().to_string_lossy().to_string();
        if name.starts_with("QF_") || matches!(name.as_str(), "BV" | "LIA" | "LRA" | "UF" | "NIA") {
            return name;
        }
    }
    "other".to_string()
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            collect(&path, out);
        } else if path.extension().is_some_and(|e| e == "smt2") {
            out.push(path);
        }
    }
}

fn run_arm(
    arena: &mut TermArena,
    input: &[TermId],
    registry: &InverterRegistry,
    totals: &mut ArmTotals,
) {
    let start = Instant::now();
    let Ok(out) = elim_unconstrained_with(arena, input, registry) else {
        return;
    };
    let micros = u64::try_from(start.elapsed().as_micros()).unwrap_or(u64::MAX);
    totals.micros += micros;
    totals.max_micros = totals.max_micros.max(micros);
    totals.eliminated += out.eliminated() as u64;
    if out.eliminated() > 0 {
        totals.files_with_firing += 1;
    }
    for (rule, count) in out.stats().rule_counts() {
        *totals.rules.entry(rule.to_string()).or_insert(0) += count;
    }
    totals.nodes_after += TermStats::compute(arena, out.assertions()).dag_nodes;
}

fn main() {
    let dirs: Vec<PathBuf> = std::env::args().skip(1).map(PathBuf::from).collect();
    assert!(
        !dirs.is_empty(),
        "usage: elim_unconstrained_ablation <dir>…"
    );
    let mut files = Vec::new();
    for dir in &dirs {
        collect(dir, &mut files);
    }
    eprintln!("{} candidate files", files.len());

    let wide = InverterRegistry::with_defaults();
    let legacy = legacy_registry();
    let off = InverterRegistry::new();

    let mut per_division: BTreeMap<String, DivisionTotals> = BTreeMap::new();
    for path in &files {
        let division = division_of(path);
        let entry = per_division.entry(division).or_default();
        entry.files += 1;
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let Ok(mut script) = parse_script(&text) else {
            continue;
        };
        // The word-level prefix the solver runs before this pass.
        let Ok(canonical) = canonicalize_terms(&mut script.arena, &script.assertions) else {
            continue;
        };
        let Ok(values) = propagate_values(&mut script.arena, &canonical.terms) else {
            continue;
        };
        let (after_values, _) = values.into_parts();
        let Ok(eqs) = solve_eqs_bounded(&mut script.arena, &after_values, DEFAULT_SOLVE_EQS_FUEL)
        else {
            continue;
        };
        let (input, _) = eqs.into_parts();
        entry.parsed += 1;
        entry.nodes_before += TermStats::compute(&script.arena, &input).dag_nodes;

        run_arm(&mut script.arena, &input, &off, &mut entry.off);
        run_arm(&mut script.arena, &input, &legacy, &mut entry.legacy);
        run_arm(&mut script.arena, &input, &wide, &mut entry.wide);
    }

    println!(
        "{:<12} {:>6} {:>10} {:>10} {:>10} {:>8} {:>8} {:>9} {:>9} {:>9}",
        "division",
        "files",
        "nodes_in",
        "n_legacy",
        "n_wide",
        "el_leg",
        "el_wide",
        "ms_off",
        "ms_legacy",
        "ms_wide",
    );
    let mut grand = DivisionTotals::default();
    for (division, t) in &per_division {
        println!(
            "{:<12} {:>6} {:>10} {:>10} {:>10} {:>8} {:>8} {:>9.1} {:>9.1} {:>9.1}",
            division,
            t.parsed,
            t.nodes_before,
            t.legacy.nodes_after,
            t.wide.nodes_after,
            t.legacy.eliminated,
            t.wide.eliminated,
            t.off.micros as f64 / 1000.0,
            t.legacy.micros as f64 / 1000.0,
            t.wide.micros as f64 / 1000.0,
        );
        grand.files += t.files;
        grand.parsed += t.parsed;
        grand.nodes_before += t.nodes_before;
        for (src, dst) in [
            (&t.off, &mut grand.off),
            (&t.legacy, &mut grand.legacy),
            (&t.wide, &mut grand.wide),
        ] {
            dst.nodes_after += src.nodes_after;
            dst.eliminated += src.eliminated;
            dst.micros += src.micros;
            dst.files_with_firing += src.files_with_firing;
            dst.max_micros = dst.max_micros.max(src.max_micros);
            for (rule, count) in &src.rules {
                *dst.rules.entry(rule.clone()).or_insert(0) += count;
            }
        }
    }
    println!(
        "{:<12} {:>6} {:>10} {:>10} {:>10} {:>8} {:>8} {:>9.1} {:>9.1} {:>9.1}",
        "TOTAL",
        grand.parsed,
        grand.nodes_before,
        grand.legacy.nodes_after,
        grand.wide.nodes_after,
        grand.legacy.eliminated,
        grand.wide.eliminated,
        grand.off.micros as f64 / 1000.0,
        grand.legacy.micros as f64 / 1000.0,
        grand.wide.micros as f64 / 1000.0,
    );
    println!();
    println!(
        "files where the pass fired: legacy {} / wide {} (of {} parsed)",
        grand.legacy.files_with_firing, grand.wide.files_with_firing, grand.parsed
    );
    println!(
        "cost per file: off {:.3} ms, legacy {:.3} ms, wide {:.3} ms  \
         (worst single file: off {:.1} ms, legacy {:.1} ms, wide {:.1} ms)",
        grand.off.micros as f64 / 1000.0 / grand.parsed.max(1) as f64,
        grand.legacy.micros as f64 / 1000.0 / grand.parsed.max(1) as f64,
        grand.wide.micros as f64 / 1000.0 / grand.parsed.max(1) as f64,
        grand.off.max_micros as f64 / 1000.0,
        grand.legacy.max_micros as f64 / 1000.0,
        grand.wide.max_micros as f64 / 1000.0,
    );
    println!("\nrule firings (wide):");
    let mut rows: Vec<(&String, &u64)> = grand.wide.rules.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    for (rule, count) in rows {
        println!("  {rule:<24} {count:>8}");
    }
}
