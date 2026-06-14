//! Pure Rust SAT-backed bit-vector backend.
//!
//! This backend is the first Phase 5 composition slice: Axeyum query terms are
//! lowered to AIG, encoded to CNF, solved through the pure-Rust `BatSat` adapter,
//! lifted back into an Axeyum model, and replayed against the original terms
//! before a `sat` result is accepted. Z3 is not used and unsupported lowering
//! remains explicit rather than falling through to an oracle.

use std::time::Duration;

// Monotonic clock: on wasm32 the browser has no `std` clock, so use `web-time`'s
// drop-in `Instant` (ADR-0017). Native targets use the std clock.
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use axeyum_bv::{
    BitLowerError, BitLowering, first_unsupported_op, first_unsupported_sort, lower_terms,
};
use axeyum_cnf::{
    CnfEncoding, CnfError, CnfFormula, ProofSolveOutcome, SatError, SatResult, check_drat,
    solve_with_drat_proof, solve_with_rustsat_batsat_timeout, tseitin_encode,
};
use axeyum_ir::{Assignment, IrError, Sort, TermArena, TermId, TermStats, Value, eval};
use axeyum_query::{Query, QueryPlan};

use crate::backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
    UnknownReason,
};
use crate::model::Model;

/// Pure Rust `QF_BV` backend for the currently supported bit-blasting subset.
///
/// The supported subset is exactly the subset accepted by `axeyum-bv` lowering,
/// which now covers the full scalar `QF_BV` operator set: Bool/BV constants and
/// symbols, Boolean connectives, BV bitwise operators, equality, `ite`,
/// `bvcomp`, concat/extract, zero/sign extension, neg/add/sub/mul, unsigned and
/// signed division and remainder (`bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod`),
/// comparisons, shifts, and constant rotates. Constructs outside the scalar
/// `QF_BV` fragment (for example arrays) would return
/// [`SolverError::Unsupported`] with no oracle fallback.
#[derive(Debug, Default)]
pub struct SatBvBackend {
    stats: Option<SolveStats>,
}

impl SatBvBackend {
    /// Creates a new pure Rust SAT-backed BV backend.
    pub fn new() -> Self {
        Self::default()
    }

    fn check_with_replay(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        replay_plan: Option<&QueryPlan>,
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        self.stats = None;
        let deadline = config
            .timeout
            .and_then(|timeout| Instant::now().checked_add(timeout));
        for &term in assertions {
            if arena.sort_of(term) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(term));
            }
        }
        if let Some((term, op)) = first_unsupported_op(arena, assertions) {
            return Err(SolverError::Unsupported(format!(
                "term #{} uses unsupported pure-Rust BV operator {op:?}",
                term.index()
            )));
        }
        if let Some((term, sort)) = first_unsupported_sort(arena, assertions) {
            return Err(SolverError::Unsupported(format!(
                "term #{} has sort {sort} that the pure-Rust BV backend cannot bit-blast",
                term.index()
            )));
        }

        let shape = TermStats::compute(arena, assertions);
        if let Some(budget) = config.node_budget
            && shape.dag_nodes > budget
        {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::NodeBudget,
                detail: format!("query has {} DAG nodes, budget {budget}", shape.dag_nodes),
            }));
        }

        let mut stats = SolveStats {
            assertion_count: assertions.len() as u64,
            terms_translated: shape.dag_nodes,
            ..SolveStats::default()
        };

        let bit_blast_start = Instant::now();
        let lowering = lower_terms(arena, assertions).map_err(map_lower_error)?;
        let bit_blast = bit_blast_start.elapsed();

        let roots = lowering
            .roots()
            .iter()
            .map(|root| root.bits()[0])
            .collect::<Vec<_>>();
        let cnf_start = Instant::now();
        let encoding =
            tseitin_encode(lowering.aig(), &roots).map_err(|error| map_cnf_error(&error))?;
        let cnf_encode = cnf_start.elapsed();
        stats.translate = bit_blast + cnf_encode;
        push_duration_ms(&mut stats, "bit_blast_ms", bit_blast);
        push_duration_ms(&mut stats, "cnf_encode_ms", cnf_encode);
        stats.backend.push((
            "aig_nodes".to_owned(),
            usize_to_f64(lowering.aig().node_count()),
        ));
        stats.backend.push((
            "aig_inputs".to_owned(),
            usize_to_f64(lowering.aig().input_count()),
        ));
        stats.backend.push((
            "cnf_variables".to_owned(),
            usize_to_f64(encoding.formula().variable_count()),
        ));
        stats.backend.push((
            "cnf_clauses".to_owned(),
            usize_to_f64(encoding.formula().clauses().len()),
        ));

        if let Some(result) = check_cnf_budgets(config, encoding.formula(), &mut stats) {
            self.stats = Some(stats);
            return Ok(result);
        }

        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            stats.solve = Duration::ZERO;
            self.stats = Some(stats);
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: "pure-Rust BV backend timeout before SAT solve".to_owned(),
            }));
        }

        let sat_timeout =
            deadline.map(|deadline| deadline.saturating_duration_since(Instant::now()));
        let solve_start = Instant::now();
        let sat_result = solve_with_rustsat_batsat_timeout(encoding.formula(), sat_timeout)
            .map_err(|error| map_sat_error(&error))?;
        stats.solve = solve_start.elapsed();

        if config.prove_unsat && matches!(sat_result, SatResult::Unsat(_)) {
            verify_unsat_proof(encoding.formula(), &mut stats)?;
        }

        let result = handle_sat_result(
            arena,
            assertions,
            replay_plan,
            &lowering,
            &encoding,
            sat_result,
            &mut stats,
        );
        self.stats = Some(stats);
        result
    }
}

impl SolverBackend for SatBvBackend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "axeyum-sat-bv rustsat-batsat".to_owned(),
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
        self.check_with_replay(arena, assertions, None, config)
    }

    fn check_query(
        &mut self,
        arena: &TermArena,
        query: &Query,
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let plan = query.plan_full(arena);
        let assertions = plan.solver_terms().collect::<Vec<_>>();
        self.check_with_replay(arena, &assertions, Some(&plan), config)
    }

    fn last_stats(&self) -> Option<&SolveStats> {
        self.stats.as_ref()
    }
}

fn complete_model(arena: &TermArena, assignment: &Assignment) -> Model {
    let mut model = Model::new();
    for (symbol, _name, sort) in arena.symbols() {
        let value = assignment
            .get(symbol)
            .unwrap_or_else(|| default_value_for_sort(sort));
        model.set(symbol, value);
    }
    model
}

fn default_value_for_sort(sort: Sort) -> Value {
    match sort {
        Sort::Bool => Value::Bool(false),
        Sort::BitVec(width) => Value::Bv { width, value: 0 },
        Sort::Array { index, element } => {
            Value::Array(axeyum_ir::ArrayValue::constant(index, element, 0))
        }
        Sort::Int => Value::Int(0),
        Sort::Real => Value::Real(axeyum_ir::Rational::zero()),
        Sort::Datatype(_) => {
            unreachable!("datatype symbols are not solved by the bit-vector backend (ADR-0022)")
        }
    }
}

fn handle_sat_result(
    arena: &TermArena,
    assertions: &[TermId],
    replay_plan: Option<&QueryPlan>,
    lowering: &BitLowering,
    encoding: &CnfEncoding,
    sat_result: SatResult,
    stats: &mut SolveStats,
) -> Result<CheckResult, SolverError> {
    match sat_result {
        SatResult::Sat(cnf_assignment) => {
            let lift_start = Instant::now();
            let aig_values = encoding
                .aig_node_values_from_assignment(lowering.aig(), &cnf_assignment)
                .map_err(|error| map_cnf_error(&error))?;
            let assignment = lowering
                .assignment_from_aig_values(&aig_values)
                .map_err(map_lower_error)?;
            let model = complete_model(arena, &assignment);
            replay_model(arena, assertions, replay_plan, &model)?;
            stats.model_lift = lift_start.elapsed();
            Ok(CheckResult::Sat(model))
        }
        SatResult::Unsat(_) => Ok(CheckResult::Unsat),
        SatResult::Unknown(reason) => {
            let kind = if reason.detail.contains("timeout") {
                UnknownKind::Timeout
            } else {
                UnknownKind::Other
            };
            Ok(CheckResult::Unknown(UnknownReason {
                kind,
                detail: reason.detail,
            }))
        }
    }
}

fn replay_model(
    arena: &TermArena,
    assertions: &[TermId],
    replay_plan: Option<&QueryPlan>,
    model: &Model,
) -> Result<(), SolverError> {
    let assignment = model.to_assignment();
    if let Some(plan) = replay_plan {
        return plan
            .replay_original(arena, &assignment)
            .map_err(|error| SolverError::Backend(format!("sat model replay failed: {error}")));
    }
    for &term in assertions {
        match eval(arena, term, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "sat model replay failed: assertion #{} evaluated to false",
                    term.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    term.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "sat model replay failed: assertion #{} failed evaluation: {error}",
                    term.index()
                )));
            }
        }
    }
    Ok(())
}

fn check_cnf_budgets(
    config: &SolverConfig,
    formula: &axeyum_cnf::CnfFormula,
    stats: &mut SolveStats,
) -> Option<CheckResult> {
    let variables = usize_to_u64(formula.variable_count());
    if let Some(budget) = config.cnf_variable_budget
        && variables > budget
    {
        stats.solve = Duration::ZERO;
        return Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::EncodingBudget,
            detail: format!("CNF has {variables} variables, budget {budget}"),
        }));
    }

    let clauses = usize_to_u64(formula.clauses().len());
    if let Some(budget) = config.cnf_clause_budget
        && clauses > budget
    {
        stats.solve = Duration::ZERO;
        return Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::EncodingBudget,
            detail: format!("CNF has {clauses} clauses, budget {budget}"),
        }));
    }

    None
}

fn map_lower_error(error: BitLowerError) -> SolverError {
    match error {
        BitLowerError::UnsupportedOp { term, op } => SolverError::Unsupported(format!(
            "term #{} uses unsupported pure-Rust BV operator {op:?}",
            term.index()
        )),
        BitLowerError::Ir(IrError::InvalidWidth(width)) => SolverError::Unsupported(format!(
            "unsupported bit-vector width {width} in pure-Rust BV backend"
        )),
        other => SolverError::Backend(other.to_string()),
    }
}

fn map_cnf_error(error: &CnfError) -> SolverError {
    SolverError::Backend(error.to_string())
}

fn map_sat_error(error: &SatError) -> SolverError {
    SolverError::Backend(error.to_string())
}

/// Independently re-derives `unsat` with the proof-producing SAT core and
/// verifies its DRAT proof (ADR-0011/0012). A disagreement (the proof core
/// finds the formula satisfiable) or a failed proof is a soundness alarm.
fn verify_unsat_proof(formula: &CnfFormula, stats: &mut SolveStats) -> Result<(), SolverError> {
    match solve_with_drat_proof(formula) {
        ProofSolveOutcome::Unsat(proof) => match check_drat(formula, &proof) {
            Ok(true) => {
                stats.backend.push(("unsat_proof_checked".to_owned(), 1.0));
                Ok(())
            }
            Ok(false) => Err(SolverError::Backend(
                "unsat proof did not derive the empty clause".to_owned(),
            )),
            Err(error) => Err(SolverError::Backend(format!(
                "unsat proof failed to check: {error}"
            ))),
        },
        ProofSolveOutcome::Sat(_) => Err(SolverError::Backend(
            "soundness alarm: adapter reported unsat but the proof core found a model".to_owned(),
        )),
        // The reference proof core exhausted its budget; the adapter's `unsat`
        // still stands, it is simply not DRAT-proof-checked.
        ProofSolveOutcome::ResourceOut => Ok(()),
    }
}

fn push_duration_ms(stats: &mut SolveStats, name: &str, duration: Duration) {
    stats
        .backend
        .push((name.to_owned(), duration.as_secs_f64() * 1000.0));
}

#[allow(clippy::cast_precision_loss)]
fn usize_to_f64(value: usize) -> f64 {
    value as f64
}

fn usize_to_u64(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}
