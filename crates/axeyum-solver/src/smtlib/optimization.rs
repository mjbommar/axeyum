//! Model-bearing text optimization; checked optimality remains a separate layer.
use super::{
    optimize_one, parse_script, smtlib_single_optimization_query, text_optimization_config,
};
use crate::{
    CheckResult, Model, OptOutcome, SolverConfig, SolverError, UnknownKind, UnknownReason,
    check_model, solve,
};
use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_smtlib::{SExpr, Script, read_all};
use std::time::Instant;

/// Source-bearing optimization certificate transport.
pub mod portable;

/// How multiple objectives share their constraints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationMode {
    /// Each optimum is independent; each row has its own feasible model.
    Box,
    /// Earlier optima are pinned before optimizing later objectives.
    Lexicographic,
}
impl OptimizationMode {
    /// Stable public mode spelling.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Box => "box",
            Self::Lexicographic => "lex",
        }
    }
}

/// One objective's decision and retained feasible witness.
#[derive(Debug, Clone)]
pub struct ObjectiveResult {
    /// Optimization engine outcome; it is not an optimality certificate.
    pub outcome: OptOutcome,
    /// True for maximize, false for minimize.
    pub maximize: bool,
    /// Original objective sort; BV order is unsigned.
    pub sort: Sort,
    /// Exact claimed optimum, or None when unresolved/infeasible/unbounded.
    pub value: Option<Value>,
    /// Why no model was retained, or None when a model is available.
    pub model_unavailable: Option<String>,
    objective: TermId,
    assertions: Vec<TermId>,
    model: Option<Model>,
    context: Vec<TermId>,
    no_better: Option<crate::lra::FarkasCertificate>,
    no_better_names: Vec<(String, bool)>,
}

/// Owns the original terms and per-objective contexts required for model replay.
#[derive(Debug)]
pub struct OptimizationReport {
    /// Explicit multiobjective semantics.
    pub mode: OptimizationMode,
    /// Decisions in active objective declaration order.
    pub objectives: Vec<ObjectiveResult>,
    script: Script,
    source: String,
}
impl OptimizationReport {
    /// Replay the original constraints/prefix and objective value; None means
    /// there is no model to check. Out-of-range indices also return None.
    ///
    /// # Errors
    /// Reports evaluator/model-check invariant failures.
    pub fn replay(&self, index: usize) -> Result<Option<bool>, SolverError> {
        let Some(row) = self.objectives.get(index) else {
            return Ok(None);
        };
        let Some(model) = &row.model else {
            return Ok(None);
        };
        if !check_model(&self.script.arena, &row.assertions, model)? {
            return Ok(Some(false));
        }
        let actual = eval(&self.script.arena, row.objective, &model.to_assignment())
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        Ok(Some(row.value.as_ref() == Some(&actual)))
    }
    /// Independently bind and replay the strict-better refutation. None means
    /// no certificate was retained; it never means checked optimality.
    ///
    /// # Errors
    /// Returns source relaxation or certificate binding errors.
    pub fn replay_optimality(&self, index: usize) -> Result<Option<bool>, SolverError> {
        let Some(row) = self.objectives.get(index) else {
            return Ok(None);
        };
        let Some(certificate) = &row.no_better else {
            return Ok(None);
        };
        let Some(Value::Int(value)) = &row.value else {
            return Ok(Some(false));
        };
        let mut arena = self.script.arena.clone();
        let bound = arena.int_const(*value);
        let better = if row.maximize {
            arena.int_gt(row.objective, bound)?
        } else {
            arena.int_lt(row.objective, bound)?
        };
        let mut query = row.context.clone();
        query.push(better);
        let Some((relaxed, assertions)) =
            crate::int_real_relax::relax_int_assertions_to_real(&arena, &query)?
        else {
            return Ok(Some(false));
        };
        certificate
            .verify_against_within(&relaxed, &assertions, None)
            .map(Some)
    }

    /// Gold eligibility requires original feasible models and source-bound
    /// no-better refutations, including every earlier lexicographic objective.
    ///
    /// # Errors
    /// Returns model or certificate replay errors.
    pub fn gold_eligible(&self, index: usize) -> Result<bool, SolverError> {
        if index >= self.objectives.len() {
            return Ok(false);
        }
        let start = if self.mode == OptimizationMode::Lexicographic {
            0
        } else {
            index
        };
        for current in start..=index {
            if self.replay(current)? != Some(true) || self.replay_optimality(current)? != Some(true)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// User-declared model entries in declaration order; absent witnesses yield
    /// an empty list, and callers must inspect model availability separately.
    #[must_use]
    pub fn model_entries(&self, index: usize) -> Vec<(String, Value)> {
        let Some(model) = self
            .objectives
            .get(index)
            .and_then(|row| row.model.as_ref())
        else {
            return vec![];
        };
        self.script
            .model_symbols
            .iter()
            .filter_map(|&s| {
                model.get(s).map(|v| {
                    (
                        self.script.arena.symbol(s).0.to_owned(),
                        super::render_string_value_for(&self.script, s, v),
                    )
                })
            })
            .collect()
    }
}

// Script's flat objective vector lacks command positions. Reconstruct the active
// indices from the exact tokenized commands before pairing it with query terms.
pub(super) fn active_objectives(
    input: &str,
    script: &Script,
) -> Result<Vec<(TermId, bool)>, SolverError> {
    let commands = read_all(input).map_err(|e| SolverError::Parse(e.to_string()))?;
    let mut active = Vec::new();
    let mut scopes = Vec::new();
    let mut queried = None;
    let mut objective_index = 0;
    for command in commands {
        let Some(items) = command.list() else {
            continue;
        };
        let head = items.first().and_then(SExpr::atom).unwrap_or("");
        match head {
            "maximize" | "minimize" => {
                active.push(objective_index);
                objective_index += 1;
            }
            "push" | "pop" => {
                let n = items
                    .get(1)
                    .and_then(SExpr::atom)
                    .unwrap_or("1")
                    .parse::<usize>()
                    .map_err(|_| SolverError::Parse("scope count".into()))?;
                if n > 4096
                    || scopes
                        .len()
                        .saturating_add(if head == "push" { n } else { 0 })
                        > 4096
                {
                    return Err(SolverError::Unsupported(
                        "OMT scope depth exceeds 4096".into(),
                    ));
                }
                if head == "push" {
                    scopes.extend(std::iter::repeat_n(active.len(), n));
                } else {
                    if n > scopes.len() {
                        return Err(SolverError::Parse("OMT pop exceeds scope depth".into()));
                    }
                    if n > 0 {
                        active.truncate(scopes[scopes.len() - n]);
                        scopes.truncate(scopes.len() - n);
                    }
                }
            }
            "reset-assertions" => {
                active.clear();
                scopes.clear();
            }
            "check-sat" | "check-sat-assuming" => {
                if queried.is_some() {
                    return Err(SolverError::Unsupported(
                        "OMT reports require one query".into(),
                    ));
                }
                queried = Some(active.clone());
            }
            _ => (),
        }
    }
    queried
        .unwrap_or(active)
        .into_iter()
        .map(|i| {
            script
                .objectives
                .get(i)
                .copied()
                .ok_or_else(|| SolverError::Backend("objective command/term mismatch".into()))
        })
        .collect()
}
fn active_priority(input: &str) -> Result<Option<String>, SolverError> {
    let mut priority = None;
    for command in read_all(input).map_err(|e| SolverError::Parse(e.to_string()))? {
        let Some(items) = command.list() else {
            continue;
        };
        match items.first().and_then(SExpr::atom) {
            Some("check-sat" | "check-sat-assuming") => break,
            Some("set-option") if items.get(1).and_then(SExpr::atom) == Some(":opt.priority") => {
                priority = items.get(2).map(SExpr::to_text);
            }
            _ => (),
        }
    }
    Ok(priority)
}
fn constant(
    arena: &mut TermArena,
    sort: Sort,
    value: i128,
) -> Result<(TermId, Value), SolverError> {
    Ok(match sort {
        Sort::Int => (arena.int_const(value), Value::Int(value)),
        Sort::BitVec(width) if width <= 127 => {
            let mask = if width >= 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            #[allow(clippy::cast_sign_loss)]
            // OptOutcome carries the unsigned BV bit pattern in i128.
            let bits = (value as u128) & mask;
            (
                arena
                    .bv_const(width, bits)
                    .map_err(|e| SolverError::Backend(e.to_string()))?,
                Value::Bv { width, value: bits },
            )
        }
        _ => return Err(SolverError::Unsupported("optimization sort".into())),
    })
}
/// Optimize the active query and retain a replayable model per objective.
/// One budget covers parsing, every optimization and witness recovery. The
/// returned report makes no checked no-better or gold-answer claim.
///
/// # Errors
/// Rejects malformed scripts, unsupported sorts/modes and solver invariants.
#[allow(clippy::too_many_lines)]
pub fn optimize_with_models(
    input: &str,
    mode: OptimizationMode,
    config: &SolverConfig,
) -> Result<OptimizationReport, SolverError> {
    let started = Instant::now();
    let mut script = parse_script(input).map_err(|e| SolverError::Parse(e.to_string()))?;
    let objectives = active_objectives(input, &script)?;
    let query = smtlib_single_optimization_query(&script)?;
    for &(objective, _) in &objectives {
        match script.arena.sort_of(objective) {
            Sort::Int | Sort::BitVec(1..=127) => (),
            sort => {
                return Err(SolverError::Unsupported(format!(
                    "optimization objective {sort:?}: reports support Int and unsigned BV widths <=127"
                )));
            }
        }
    }
    if let Some(requested) = active_priority(input)? {
        if requested != mode.name() {
            return Err(SolverError::Unsupported(format!(
                "script opt.priority {requested} conflicts with explicit {} mode",
                mode.name()
            )));
        }
    }
    if objectives.is_empty() {
        return Err(SolverError::Unsupported(
            "no active optimization objectives".into(),
        ));
    }
    let mut assertions = query.assertions;
    let mut rows = Vec::new();
    let mut stopped = false;
    for (objective, maximize) in objectives {
        let sort = script.arena.sort_of(objective);
        let outcome = if stopped {
            OptOutcome::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "higher-priority objective has no optimum".into(),
            })
        } else {
            optimize_one(
                &mut script.arena,
                &assertions,
                objective,
                maximize,
                &text_optimization_config(config, started),
            )?
        };
        let mut row = ObjectiveResult {
            outcome,
            maximize,
            sort,
            value: None,
            model_unavailable: Some("objective has no attained optimum".into()),
            objective,
            assertions: assertions.clone(),
            model: None,
            context: assertions.clone(),
            no_better: None,
            no_better_names: Vec::new(),
        };
        if let OptOutcome::Optimal(value) = row.outcome {
            let (term, exact) = constant(&mut script.arena, sort, value)?;
            let pin = script
                .arena
                .eq(objective, term)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            row.value = Some(exact);
            row.assertions.push(pin);
            let remaining = text_optimization_config(config, started);
            if remaining.timeout.is_some_and(|t| t.is_zero()) {
                row.model_unavailable =
                    Some("shared timeout reached before witness recovery".into());
            } else {
                match solve(&mut script.arena, &row.assertions, &remaining)? {
                    CheckResult::Sat(model) => {
                        row.model = Some(model);
                        row.model_unavailable = None;
                    }
                    CheckResult::Unknown(reason) => row.model_unavailable = Some(reason.detail),
                    CheckResult::Unsat => {
                        return Err(SolverError::Backend(
                            "optimizer optimum has no feasible witness".into(),
                        ));
                    }
                }
            }
            if mode == OptimizationMode::Lexicographic {
                assertions.push(pin);
            }
        }
        stopped = mode == OptimizationMode::Lexicographic
            && !matches!(row.outcome, OptOutcome::Optimal(_));
        rows.push(row);
    }
    let mut report = OptimizationReport {
        mode,
        objectives: rows,
        script,
        source: input.to_owned(),
    };
    // All original symbol declarations are now fixed. Generate certificates
    // against this final arena so later objective solves cannot shift the
    // fresh relaxation column IDs used when replay reconstructs the source.
    for row in &mut report.objectives {
        if row.sort != Sort::Int || row.model.is_none() {
            continue;
        }
        let Some(Value::Int(value)) = &row.value else {
            continue;
        };
        let remaining = text_optimization_config(config, started);
        if remaining.timeout.is_some_and(|t| t.is_zero()) {
            break;
        }
        let bound = report.script.arena.int_const(*value);
        let better = if row.maximize {
            report.script.arena.int_gt(row.objective, bound)?
        } else {
            report.script.arena.int_lt(row.objective, bound)?
        };
        // Never include this objective's optimum pin in the refutation.
        let mut query = row.context.clone();
        query.push(better);
        if let Some((relaxed, constraints)) =
            crate::int_real_relax::relax_int_assertions_to_real(&report.script.arena, &query)?
        {
            let deadline = config.timeout.and_then(|t| started.checked_add(t));
            row.no_better =
                match crate::lra::lra_farkas_certificate_within(&relaxed, &constraints, deadline) {
                    Ok(certificate) => certificate,
                    Err(SolverError::Unsupported(_)) => None,
                    Err(error) => return Err(error),
                };
            if let Some(certificate) = &row.no_better {
                row.no_better_names = certificate
                    .vars
                    .iter()
                    .map(|&symbol| {
                        let name = relaxed.symbol(symbol).0;
                        (
                            name.to_owned(),
                            relaxed.find_internal_symbol(name) == Some(symbol),
                        )
                    })
                    .collect();
            }
            if deadline.is_some_and(|d| Instant::now() >= d) {
                row.no_better = None;
            }
        }
    }
    for index in 0..report.objectives.len() {
        if report.replay(index)? == Some(false) {
            return Err(SolverError::Backend(
                "optimization model/value replay failed".into(),
            ));
        }
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    const BOUNDS: &str = "(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)(assert (and (>= x 0) (<= x 10) (>= y 0) (<= y 3)))";
    fn config() -> SolverConfig {
        SolverConfig::new().with_timeout(std::time::Duration::from_secs(10))
    }
    fn run(q: &str, mode: OptimizationMode) -> OptimizationReport {
        optimize_with_models(q, mode, &config()).unwrap()
    }
    #[test]
    fn attained_integer_values_replay_and_modes_differ() {
        let q = format!("{BOUNDS}(assert (<= (+ x y) 10))(maximize x)(maximize y)(check-sat)");
        for (mode, ys) in [
            (OptimizationMode::Box, 3),
            (OptimizationMode::Lexicographic, 0),
        ] {
            let r = run(&q, mode);
            assert_eq!(r.objectives[0].value, Some(Value::Int(10)));
            assert_eq!(r.objectives[1].value, Some(Value::Int(ys)));
            assert_eq!(r.replay(0).unwrap(), Some(true));
            assert_eq!(r.replay(1).unwrap(), Some(true));
            assert_eq!(r.replay_optimality(0).unwrap(), Some(true));
            assert_eq!(r.replay_optimality(1).unwrap(), Some(true));
        }
        let r = run(
            &format!("{BOUNDS}(minimize x)(check-sat)"),
            OptimizationMode::Box,
        );
        assert_eq!(r.objectives[0].value, Some(Value::Int(0)));
        assert_eq!(r.replay(0).unwrap(), Some(true));
    }
    #[test]
    fn strict_better_certificate_excludes_the_optimum_pin() {
        for direction in ["maximize", "minimize"] {
            let mut report = run(
                &format!("{BOUNDS}({direction} x)(check-sat)"),
                OptimizationMode::Box,
            );
            assert_eq!(report.replay_optimality(0).unwrap(), Some(true));
            report.objectives[0].value =
                Some(Value::Int(if direction == "maximize" { 9 } else { 1 }));
            assert_eq!(report.replay_optimality(0).unwrap(), Some(false));
        }
    }

    #[test]
    fn integer_cut_required_optimum_has_no_real_refutation() {
        let report = run(
            "(declare-const x Int)(assert (>= x 0))(assert (<= (* 2 x) 1))(maximize x)(check-sat)",
            OptimizationMode::Box,
        );
        assert_eq!(report.objectives[0].value, Some(Value::Int(0)));
        assert_eq!(report.replay(0).unwrap(), Some(true));
        assert_eq!(report.replay_optimality(0).unwrap(), None);
    }

    #[test]
    fn gold_credit_requires_every_lexicographic_prefix_refutation() {
        let query = "(declare-const x Int)(declare-const y Int)(assert (>= x 0))(assert (<= (* 2 x) 1))(assert (and (>= y 0) (<= y 3)))(maximize x)(maximize y)(check-sat)";
        for mode in [OptimizationMode::Box, OptimizationMode::Lexicographic] {
            let report = run(query, mode);
            assert_eq!(report.replay_optimality(0).unwrap(), None);
            assert_eq!(report.replay_optimality(1).unwrap(), Some(true));
            assert!(!report.gold_eligible(0).unwrap());
            assert_eq!(
                report.gold_eligible(1).unwrap(),
                mode == OptimizationMode::Box
            );
            assert!(!report.gold_eligible(2).unwrap());
        }
    }

    #[test]
    fn original_objective_value_tampering_fails_replay() {
        let mut r = run(
            &format!("{BOUNDS}(maximize x)(check-sat)"),
            OptimizationMode::Box,
        );
        r.objectives[0].value = Some(Value::Int(11));
        assert_eq!(r.replay(0).unwrap(), Some(false));
    }
    #[test]
    fn original_constraint_model_tampering_fails_replay() {
        let mut r = run(
            &format!("{BOUNDS}(maximize x)(check-sat)"),
            OptimizationMode::Box,
        );
        let y = r.script.arena.find_symbol("y").unwrap();
        r.objectives[0]
            .model
            .as_mut()
            .unwrap()
            .set(y, Value::Int(20));
        assert_eq!(r.replay(0).unwrap(), Some(false));
    }
    #[test]
    fn objective_scope_and_query_snapshot_match_assertions() {
        let q = format!("{BOUNDS}(maximize x)(push 1)(minimize x)(pop 1)(check-sat)(minimize y)");
        let r = run(&q, OptimizationMode::Box);
        assert_eq!(r.objectives.len(), 1);
        assert_eq!(r.objectives[0].value, Some(Value::Int(10)));
        assert_eq!(
            super::super::optimize_smtlib(&q, &config()).unwrap(),
            vec![OptOutcome::Optimal(10)]
        );
        assert_eq!(
            super::super::optimize_smtlib_lexicographic(&q, &config()).unwrap(),
            vec![OptOutcome::Optimal(10)]
        );
        let q = format!(
            "{BOUNDS}(maximize x)(reset-assertions)(assert (and (>= x 0) (<= x 4)))(minimize x)(check-sat)"
        );
        let r = run(&q, OptimizationMode::Lexicographic);
        assert_eq!(r.objectives.len(), 1);
        assert_eq!(r.objectives[0].value, Some(Value::Int(0)));
    }
    #[test]
    fn unresolved_prefix_budget_and_infeasibility_remain_distinct() {
        let q = "(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)(assert (and (>= y 0) (<= y 3)))(maximize x)(maximize y)(check-sat)";
        let r = run(q, OptimizationMode::Lexicographic);
        assert_eq!(r.objectives[0].outcome, OptOutcome::Unbounded);
        assert!(matches!(r.objectives[1].outcome, OptOutcome::Unknown(_)));
        let r = run(q, OptimizationMode::Box);
        assert_eq!(r.objectives[1].value, Some(Value::Int(3)));
        let q = format!("{BOUNDS}(maximize x)(check-sat)");
        let c = SolverConfig::new().with_timeout(std::time::Duration::ZERO);
        let r = optimize_with_models(&q, OptimizationMode::Box, &c).unwrap();
        assert!(matches!(r.objectives[0].outcome, OptOutcome::Unknown(_)));
        assert_eq!(r.replay(0).unwrap(), None);
        let r = run(
            &format!("{BOUNDS}(assert (< x 0))(maximize x)(check-sat)"),
            OptimizationMode::Box,
        );
        assert_eq!(r.objectives[0].outcome, OptOutcome::Infeasible);
        assert_eq!(r.replay(0).unwrap(), None);
    }
    #[test]
    fn unsupported_modes_sorts_and_empty_requests_are_explicit() {
        for q in [
            "(declare-const r Real)(maximize r)(check-sat)",
            "(declare-const x Int)(check-sat)",
            "(declare-const x Int)(maximize x)(set-option :opt.priority pareto)(check-sat)",
        ] {
            assert!(matches!(
                optimize_with_models(q, OptimizationMode::Lexicographic, &config()),
                Err(SolverError::Unsupported(_))
            ));
        }
        let q = format!("{BOUNDS}(maximize x)(check-sat)(set-option :opt.priority pareto)");
        assert_eq!(
            run(&q, OptimizationMode::Box).objectives[0].value,
            Some(Value::Int(10))
        );
    }
    #[test]
    fn unsigned_bv_optimum_has_exact_value_and_model() {
        let q = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (bvult x (_ bv200 8)))(maximize x)(check-sat)";
        let r = run(q, OptimizationMode::Box);
        assert_eq!(
            r.objectives[0].value,
            Some(Value::Bv {
                width: 8,
                value: 199
            })
        );
        assert_eq!(r.replay(0).unwrap(), Some(true));
        let r = run(
            "(set-logic QF_BV)(declare-const x (_ BitVec 127))(maximize x)(check-sat)",
            OptimizationMode::Box,
        );
        assert_eq!(
            r.objectives[0].value,
            Some(Value::Bv {
                width: 127,
                value: (1u128 << 127) - 1
            })
        );
        assert_eq!(r.replay(0).unwrap(), Some(true));
        assert!(matches!(
            optimize_with_models(
                "(declare-const x (_ BitVec 128))(maximize x)(check-sat)",
                OptimizationMode::Box,
                &config()
            ),
            Err(SolverError::Unsupported(_))
        ));
    }
}
