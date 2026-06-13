//! Developer diagnostic for replay-refined `sat-bv` plans.
//!
//! The example follows the benchmark harness' replay-refinement loop for one
//! SMT-LIB instance, then prints the final submitted operator mix and backend
//! AIG/CNF counters. It is intentionally outside the public CLI because the
//! output is for local encoding work, not stable artifact schema.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::error::Error;
use std::fs;
use std::time::Duration;

use axeyum_ir::{TermArena, TermId, TermNode, TermStats, Value, eval, render};
use axeyum_query::{Query, QueryPlan};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, SatBvBackend, SolveStats, SolverBackend, SolverConfig, UnknownKind,
};

type ReplayFailures = Vec<(usize, TermId)>;

const PLAN_REFINE_SCORE_CANDIDATES: usize = 64;

#[derive(Clone, Copy)]
struct ProfileOptions {
    verbose: bool,
    exact: bool,
    adaptive_batch: bool,
    refine_select: RefineSelectMode,
    max_rounds: usize,
    batch_size: usize,
}

impl ProfileOptions {
    fn from_env() -> Self {
        Self {
            verbose: env::var_os("AXEYUM_PROFILE_VERBOSE").is_some(),
            exact: env::var_os("AXEYUM_PROFILE_EXACT").is_some(),
            adaptive_batch: env::var_os("AXEYUM_PROFILE_ADAPTIVE_BATCH").is_some(),
            refine_select: RefineSelectMode::from_env(),
            max_rounds: env_usize("AXEYUM_PROFILE_ROUNDS", 16).max(1),
            batch_size: env_usize("AXEYUM_PROFILE_REFINE_BATCH", 1).max(1),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RefineSelectMode {
    First,
    SmallestDag,
    SmallestPlanDag,
    SmallestPlanGreedy,
}

impl RefineSelectMode {
    fn from_env() -> Self {
        match env::var("AXEYUM_PROFILE_REFINE_SELECT").as_deref() {
            Ok("smallest-dag") => Self::SmallestDag,
            Ok("smallest-plan-dag") => Self::SmallestPlanDag,
            Ok("smallest-plan-greedy") => Self::SmallestPlanGreedy,
            _ => Self::First,
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let Some(path) = env::args().nth(1) else {
        eprintln!("usage: replay_refine_profile <file.smt2>");
        std::process::exit(2);
    };

    let text = fs::read_to_string(&path)?;
    let script = parse_script(&text)?;
    let query = query_for_assertions(&script.arena, &script.assertions)?;
    let mut backend = SatBvBackend::new();
    let config = SolverConfig {
        timeout: Some(Duration::from_millis(env_u64(
            "AXEYUM_PROFILE_TIMEOUT_MS",
            1000,
        ))),
        node_budget: Some(env_u64("AXEYUM_PROFILE_NODE_BUDGET", 5000)),
        cnf_variable_budget: Some(env_u64("AXEYUM_PROFILE_CNF_VAR_BUDGET", 7000)),
        cnf_clause_budget: Some(env_u64("AXEYUM_PROFILE_CNF_CLAUSE_BUDGET", 20000)),
        ..SolverConfig::default()
    };
    run_profile_loop(
        &script.arena,
        &script.assertions,
        &query,
        &mut backend,
        &config,
        ProfileOptions::from_env(),
    )?;
    Ok(())
}

fn run_profile_loop(
    arena: &TermArena,
    assertions: &[TermId],
    query: &Query,
    backend: &mut SatBvBackend,
    config: &SolverConfig,
    options: ProfileOptions,
) -> Result<(), Box<dyn Error>> {
    let mut batch_size = options.batch_size;
    let mut targets = assertions.first().copied().into_iter().collect::<Vec<_>>();
    let mut previous_solver_terms = BTreeSet::new();
    let mut last_added_terms = Vec::new();
    let mut adaptive_backoffs = 0usize;
    for round in 1..=options.max_rounds {
        let plan = if options.exact {
            query.slice_exact_targets(arena, &targets)
        } else {
            query.slice_for_targets(arena, &targets)
        };
        let solver_terms = plan.solver_terms().collect::<Vec<_>>();
        let new_solver_terms = solver_terms
            .iter()
            .copied()
            .filter(|term| !previous_solver_terms.contains(term))
            .collect::<Vec<_>>();
        let result = backend.check(arena, &solver_terms, config);
        let stats = backend.last_stats().cloned().unwrap_or_default();

        print_round_profile(
            arena,
            round,
            &plan,
            targets.len(),
            &new_solver_terms,
            &stats,
            options.verbose,
        );
        previous_solver_terms = solver_terms.iter().copied().collect();

        match result {
            Ok(CheckResult::Sat(model)) => {
                if let Some(failures) = failed_assertion_batch(
                    arena,
                    assertions,
                    &model,
                    FailureSelection {
                        current_targets: &targets,
                        batch_size,
                        select_mode: options.refine_select,
                        query,
                        exact_targets: options.exact,
                    },
                )? {
                    let (failed_index, failed) = failures[0];
                    println!(
                        "sat-subset failed full replay at assertion #{failed_index} term #{}",
                        failed.index()
                    );
                    if options.verbose {
                        println!("failed_assertion={}", compact_render(arena, failed));
                    }
                    if targets.contains(&failed) {
                        break;
                    }
                    last_added_terms = failures.into_iter().map(|(_, term)| term).collect();
                    targets.extend(last_added_terms.iter().copied());
                } else {
                    println!("sat after full replay");
                    profile_terms_with_label("operator_counts", arena, &solver_terms);
                    break;
                }
            }
            Ok(CheckResult::Unsat) => {
                println!("unsat subset");
                profile_terms_with_label("operator_counts", arena, &solver_terms);
                break;
            }
            Ok(CheckResult::Unknown(reason)) => {
                if round < options.max_rounds
                    && try_adaptive_backoff(
                        options.adaptive_batch,
                        reason.kind,
                        &mut targets,
                        &mut last_added_terms,
                        &mut batch_size,
                        &mut adaptive_backoffs,
                    )
                {
                    continue;
                }
                println!("unknown {:?}: {}", reason.kind, reason.detail);
                profile_terms_with_label("operator_counts", arena, &solver_terms);
                break;
            }
            Err(error) => {
                println!("error: {error}");
                profile_terms_with_label("operator_counts", arena, &solver_terms);
                break;
            }
        }
    }

    Ok(())
}

fn print_round_profile(
    arena: &TermArena,
    round: usize,
    plan: &QueryPlan,
    target_terms: usize,
    new_solver_terms: &[TermId],
    stats: &SolveStats,
    verbose: bool,
) {
    println!(
        "round={round} planned_terms={} new_planned_terms={} dropped_terms={} target_terms={} dag_nodes={} tree_nodes={} digest={:016x}",
        plan.planned_terms().len(),
        new_solver_terms.len(),
        plan.dropped_terms().len(),
        target_terms,
        plan.solver_cache_key().dag_nodes,
        plan.solver_cache_key().tree_nodes,
        plan.solver_cache_key().digest,
    );
    println!("backend_stats={:?}", stats.backend);
    if verbose && !new_solver_terms.is_empty() {
        println!("new_terms:");
        for term in new_solver_terms {
            println!("  #{} {}", term.index(), compact_render(arena, *term));
        }
        profile_terms_with_label("new_operator_counts", arena, new_solver_terms);
    }
}

fn try_adaptive_backoff(
    adaptive_batch: bool,
    unknown_kind: UnknownKind,
    targets: &mut Vec<TermId>,
    last_added_terms: &mut Vec<TermId>,
    batch_size: &mut usize,
    adaptive_backoffs: &mut usize,
) -> bool {
    if !adaptive_batch || unknown_kind != UnknownKind::EncodingBudget || last_added_terms.len() <= 1
    {
        return false;
    }

    let base_len = targets.len() - last_added_terms.len();
    let reduced_len = (last_added_terms.len() / 2).max(1);
    let reduced_terms = last_added_terms[..reduced_len].to_vec();
    targets.truncate(base_len);
    targets.extend(reduced_terms.iter().copied());
    *last_added_terms = reduced_terms;
    *batch_size = (*batch_size).min(reduced_len).max(1);
    *adaptive_backoffs += 1;
    println!(
        "adaptive-backoff #{}: retry with batch_size={} target_terms={}",
        *adaptive_backoffs,
        *batch_size,
        targets.len()
    );
    true
}

fn query_for_assertions(arena: &TermArena, assertions: &[TermId]) -> Result<Query, Box<dyn Error>> {
    let mut builder = Query::builder(arena);
    for &assertion in assertions {
        builder.assert(assertion)?;
    }
    Ok(builder.build())
}

fn failed_assertion_batch(
    arena: &TermArena,
    assertions: &[TermId],
    model: &axeyum_solver::Model,
    selection: FailureSelection<'_>,
) -> Result<Option<ReplayFailures>, Box<dyn Error>> {
    let assignment = model.to_assignment();
    let current_target_set = selection
        .current_targets
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut saw_failure = false;
    let mut failures = Vec::new();
    let mut candidates = Vec::new();
    for (index, &assertion) in assertions.iter().enumerate() {
        if eval(arena, assertion, &assignment)? != Value::Bool(true) {
            saw_failure = true;
            if current_target_set.contains(&assertion) {
                return Ok(Some(vec![(index, assertion)]));
            }
            match selection.select_mode {
                RefineSelectMode::First => {
                    failures.push((index, assertion));
                    if failures.len() >= selection.batch_size {
                        break;
                    }
                }
                RefineSelectMode::SmallestDag
                | RefineSelectMode::SmallestPlanDag
                | RefineSelectMode::SmallestPlanGreedy => {
                    candidates.push((failure_score(arena, assertion), index, assertion));
                }
            }
        }
    }
    if selection.select_mode != RefineSelectMode::First {
        failures = select_scored_failures(arena, candidates, selection);
    }
    if saw_failure && failures.is_empty() {
        return Err("replay failed but no failed assertion was selected".into());
    }
    Ok((!failures.is_empty()).then_some(failures))
}

#[derive(Clone, Copy)]
struct FailureSelection<'a> {
    current_targets: &'a [TermId],
    batch_size: usize,
    select_mode: RefineSelectMode,
    query: &'a Query,
    exact_targets: bool,
}

fn select_scored_failures(
    arena: &TermArena,
    mut candidates: Vec<(FailureScore, usize, TermId)>,
    selection: FailureSelection<'_>,
) -> ReplayFailures {
    candidates.sort_by_key(|(score, index, term)| (*score, *index, *term));
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
            candidates = candidates
                .into_iter()
                .map(|(_, index, term)| {
                    (
                        plan_failure_score(
                            arena,
                            selection.query,
                            selection.current_targets,
                            &[],
                            term,
                            selection.exact_targets,
                        ),
                        index,
                        term,
                    )
                })
                .collect::<Vec<_>>();
            candidates.sort_by_key(|(score, index, term)| (*score, *index, *term));
        }
    }
    candidates
        .into_iter()
        .take(selection.batch_size)
        .map(|(_, index, term)| (index, term))
        .collect()
}

fn select_plan_greedy_failures(
    arena: &TermArena,
    mut candidates: Vec<(FailureScore, usize, TermId)>,
    selection: FailureSelection<'_>,
) -> ReplayFailures {
    let mut selected = Vec::new();
    let mut selected_terms = Vec::new();
    while selected.len() < selection.batch_size && !candidates.is_empty() {
        for (score, _, term) in &mut candidates {
            *score = plan_failure_score(
                arena,
                selection.query,
                selection.current_targets,
                &selected_terms,
                *term,
                selection.exact_targets,
            );
        }
        candidates.sort_by_key(|(score, index, term)| (*score, *index, *term));
        let (_, index, term) = candidates.remove(0);
        selected_terms.push(term);
        selected.push((index, term));
    }
    selected
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct FailureScore {
    dag_nodes: u64,
    tree_nodes: u64,
    ite_count: u64,
    term_index: usize,
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

fn env_usize(name: &str, default: usize) -> usize {
    env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn env_u64(name: &str, default: u64) -> u64 {
    env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn compact_render(arena: &TermArena, term: TermId) -> String {
    const LIMIT: usize = 360;
    let rendered = render(arena, term);
    if rendered.len() <= LIMIT {
        rendered
    } else {
        format!("{}...", &rendered[..LIMIT])
    }
}

fn profile_terms_with_label(label: &str, arena: &TermArena, roots: &[TermId]) {
    let mut counts = BTreeMap::<String, u64>::new();
    let mut widths = BTreeMap::<String, u64>::new();
    let mut visited = BTreeSet::new();
    let mut stack = roots.to_vec();

    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::BoolConst(_) => {
                *counts.entry("BoolConst".to_owned()).or_default() += 1;
            }
            TermNode::BvConst { width, .. } => {
                *counts.entry("BvConst".to_owned()).or_default() += 1;
                *widths.entry(format!("const_bv{width}")).or_default() += 1;
            }
            TermNode::IntConst(_) => {
                *counts.entry("IntConst".to_owned()).or_default() += 1;
            }
            TermNode::RealConst(_) => {
                *counts.entry("RealConst".to_owned()).or_default() += 1;
            }
            TermNode::Symbol(symbol) => {
                let (_, sort) = arena.symbol(*symbol);
                *counts.entry(format!("Symbol({sort})")).or_default() += 1;
            }
            TermNode::App { op, args } => {
                *counts.entry(format!("{op:?}")).or_default() += 1;
                stack.extend(args.iter().copied());
            }
        }
    }

    println!("{label}:");
    for (key, value) in counts {
        println!("  {key}: {value}");
    }
    println!("constant_widths:");
    for (key, value) in widths {
        println!("  {key}: {value}");
    }
}
