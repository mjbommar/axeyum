//! The Z3 oracle backend (feature `z3`).
//!
//! Per ADR-0002, this backend is bootstrap scaffolding with a planned
//! demotion path; it exists so every Axeyum layer is built against a mature
//! referee. It translates Axeyum terms to Z3 ASTs, checks, and lifts models
//! back to Axeyum symbols. Z3 types never leak across this module's
//! boundary.
//!
//! # Example (milestone M0 doctest, ADR-0001)
//!
//! `x + 1 == 5` over `BV(8)` solves via Z3 and the lifted model is
//! confirmed by the trusted evaluator:
//!
//! ```
//! use axeyum_ir::{Sort, TermArena, Value, eval};
//! use axeyum_solver::{CheckResult, SolverBackend, SolverConfig, Z3Backend};
//!
//! let mut arena = TermArena::new();
//! let x_sym = arena.declare("x", Sort::BitVec(8))?;
//! let x = arena.var(x_sym);
//! let one = arena.bv_const(8, 1)?;
//! let five = arena.bv_const(8, 5)?;
//! let sum = arena.bv_add(x, one)?;
//! let formula = arena.eq(sum, five)?;
//!
//! let mut backend = Z3Backend::new();
//! let outcome = backend.check(&arena, &[formula], &SolverConfig::default())?;
//!
//! let CheckResult::Sat(model) = outcome else { panic!("expected sat") };
//! assert_eq!(model.get(x_sym), Some(Value::Bv { width: 8, value: 4 }));
//!
//! // Untrusted search, trusted checking: replay the model through the
//! // ground evaluator against the original formula.
//! assert_eq!(
//!     eval(&arena, formula, &model.to_assignment())?,
//!     Value::Bool(true)
//! );
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use std::collections::HashMap;

use std::time::Instant;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode, TermStats, Value};
use z3::ast::{BV, Bool};
use z3::{Config, Params, SatResult, Solver, with_z3_config};

use crate::backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
    UnknownReason,
};
use crate::model::Model;

/// Z3 oracle backend. Stateless across queries except for the telemetry of
/// the most recent check.
#[derive(Debug, Default)]
pub struct Z3Backend {
    stats: Option<SolveStats>,
}

impl Z3Backend {
    /// Creates a new backend instance.
    pub fn new() -> Self {
        Self::default()
    }
}

impl SolverBackend for Z3Backend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: format!("z3 {}", z3::full_version()),
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
        self.stats = None;
        for &t in assertions {
            if arena.sort_of(t) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(t));
            }
        }
        // Admission control: refuse to translate past the node budget.
        let shape = TermStats::compute(arena, assertions);
        if let Some(budget) = config.node_budget
            && shape.dag_nodes > budget
        {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::NodeBudget,
                detail: format!("query has {} DAG nodes, budget {budget}", shape.dag_nodes),
            }));
        }
        // Z3's memory cap is process-global (observability note caveat), so
        // any per-query setting is restored when this check returns.
        let _memory_guard = config.memory_limit_mb.map(|mb| {
            let value = mb.to_string();
            Z3GlobalParamGuard::set("memory_max_size", &value)
        });
        let mut cfg = Config::new();
        cfg.set_model_generation(true);
        // The closure runs against a scoped thread-local Z3 context; no Z3
        // object survives past it.
        let (result, stats) = with_z3_config(&cfg, || run_check(arena, assertions, config));
        self.stats = Some(stats);
        result
    }

    fn last_stats(&self) -> Option<&SolveStats> {
        self.stats.as_ref()
    }
}

struct Z3GlobalParamGuard {
    key: &'static str,
    previous: Option<String>,
}

impl Z3GlobalParamGuard {
    fn set(key: &'static str, value: &str) -> Self {
        let previous = z3::get_global_param(key);
        z3::set_global_param(key, value);
        Self { key, previous }
    }
}

impl Drop for Z3GlobalParamGuard {
    fn drop(&mut self) {
        if let Some(previous) = &self.previous {
            z3::set_global_param(self.key, previous);
        } else {
            z3::reset_all_global_params();
        }
    }
}

/// Classifies Z3's `reason_unknown` strings into structured kinds.
fn classify_unknown(detail: &str) -> UnknownKind {
    let lower = detail.to_lowercase();
    if lower.contains("timeout") || lower.contains("canceled") || lower.contains("cancelled") {
        UnknownKind::Timeout
    } else if lower.contains("resource") || lower.contains("rlimit") {
        UnknownKind::ResourceLimit
    } else if lower.contains("memory") {
        UnknownKind::MemoryLimit
    } else if lower.contains("incomplete") {
        UnknownKind::Incomplete
    } else {
        UnknownKind::Other
    }
}

/// A translated term: Z3 splits Bool and BV at the type level.
#[derive(Clone)]
enum Z3Term {
    B(Bool),
    V(BV),
}

impl Z3Term {
    fn as_bool(&self) -> &Bool {
        match self {
            Z3Term::B(b) => b,
            Z3Term::V(_) => unreachable!("builder-checked Bool position"),
        }
    }

    fn as_bv(&self) -> &BV {
        match self {
            Z3Term::V(v) => v,
            Z3Term::B(_) => unreachable!("builder-checked BitVec position"),
        }
    }
}

fn run_check(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> (Result<CheckResult, SolverError>, SolveStats) {
    let mut stats = SolveStats {
        assertion_count: assertions.len() as u64,
        ..SolveStats::default()
    };
    let translate_start = Instant::now();
    let mut cache: HashMap<TermId, Z3Term> = HashMap::new();
    let solver = Solver::new();
    let mut params = Params::new();
    if let Some(timeout) = config.timeout {
        params.set_u32(
            "timeout",
            u32::try_from(timeout.as_millis()).unwrap_or(u32::MAX),
        );
    }
    if let Some(rlimit) = config.resource_limit {
        params.set_u32("rlimit", u32::try_from(rlimit).unwrap_or(u32::MAX));
    }
    solver.set_params(&params);
    for &t in assertions {
        match translate(arena, t, &mut cache) {
            Ok(translated) => solver.assert(translated.as_bool()),
            Err(e) => return (Err(e), stats),
        }
    }
    stats.terms_translated = cache.len() as u64;
    stats.translate = translate_start.elapsed();

    let solve_start = Instant::now();
    let sat_result = solver.check();
    stats.solve = solve_start.elapsed();
    for entry in solver.get_statistics().entries() {
        let value = match entry.value {
            z3::StatisticsValue::UInt(u) => f64::from(u),
            z3::StatisticsValue::Double(d) => d,
        };
        stats.backend.push((entry.key.clone(), value));
    }

    let result = match sat_result {
        SatResult::Unsat => Ok(CheckResult::Unsat),
        SatResult::Unknown => {
            let detail = solver
                .get_reason_unknown()
                .unwrap_or_else(|| "unknown".to_owned());
            Ok(CheckResult::Unknown(UnknownReason {
                kind: classify_unknown(&detail),
                detail,
            }))
        }
        SatResult::Sat => {
            let lift_start = Instant::now();
            let lifted = lift_model(arena, &solver).map(CheckResult::Sat);
            stats.model_lift = lift_start.elapsed();
            lifted
        }
    };
    (result, stats)
}

/// Lifts the backend model to Axeyum symbols.
fn lift_model(arena: &TermArena, solver: &Solver) -> Result<Model, SolverError> {
    let z3_model = solver
        .get_model()
        .ok_or_else(|| SolverError::Backend("sat result without model".to_owned()))?;
    let mut model = Model::new();
    for (sym, name, sort) in arena.symbols() {
        let value = match sort {
            Sort::Array { .. } => {
                return Err(SolverError::Unsupported(
                    "z3 oracle does not lift array models".to_owned(),
                ));
            }
            Sort::Int => {
                return Err(SolverError::Unsupported(
                    "z3 oracle does not lift integer models yet (ADR-0014)".to_owned(),
                ));
            }
            Sort::Real => {
                return Err(SolverError::Unsupported(
                    "z3 oracle does not lift real models yet (ADR-0015)".to_owned(),
                ));
            }
            Sort::Datatype(_) => {
                return Err(SolverError::Unsupported(
                    "z3 oracle does not lift datatype models yet (ADR-0022)".to_owned(),
                ));
            }
            Sort::Bool => {
                let ast = Bool::new_const(name);
                let v = z3_model
                    .eval(&ast, true)
                    .and_then(|b| b.as_bool())
                    .ok_or_else(|| model_error(name))?;
                Value::Bool(v)
            }
            Sort::BitVec(width) => {
                let ast = BV::new_const(name, width);
                let v = lift_bv(&z3_model, &ast, width).ok_or_else(|| model_error(name))?;
                Value::Bv { width, value: v }
            }
        };
        model.set(sym, value);
    }
    Ok(model)
}

fn model_error(name: &str) -> SolverError {
    SolverError::Backend(format!("could not lift model value for symbol `{name}`"))
}

/// Extracts a bit-vector model value, in 64-bit chunks for wide vectors.
fn lift_bv(model: &z3::Model, ast: &BV, width: u32) -> Option<u128> {
    if width <= 64 {
        let v = model.eval(ast, true)?.as_u64()?;
        Some(u128::from(v))
    } else {
        let lo = model.eval(&ast.extract(63, 0), true)?.as_u64()?;
        let hi = model.eval(&ast.extract(width - 1, 64), true)?.as_u64()?;
        Some((u128::from(hi) << 64) | u128::from(lo))
    }
}

#[allow(clippy::too_many_lines)]
fn translate(
    arena: &TermArena,
    root: TermId,
    cache: &mut HashMap<TermId, Z3Term>,
) -> Result<Z3Term, SolverError> {
    // Iterative post-order, mirroring the evaluator, so deep terms cannot
    // overflow the stack.
    let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
    while let Some((t, children_ready)) = stack.pop() {
        if cache.contains_key(&t) {
            continue;
        }
        let node = arena.node(t);
        match node {
            TermNode::BoolConst(b) => {
                cache.insert(t, Z3Term::B(Bool::from_bool(*b)));
            }
            TermNode::BvConst { width, value } => {
                cache.insert(t, Z3Term::V(bv_constant(*width, *value)?));
            }
            TermNode::IntConst(_) => {
                return Err(SolverError::Unsupported(
                    "z3 oracle does not support integer terms yet (ADR-0014)".to_owned(),
                ));
            }
            TermNode::RealConst(_) => {
                return Err(SolverError::Unsupported(
                    "z3 oracle does not support real terms yet (ADR-0015)".to_owned(),
                ));
            }
            TermNode::Symbol(s) => {
                let (name, sort) = arena.symbol(*s);
                let term = match sort {
                    Sort::Bool => Z3Term::B(Bool::new_const(name)),
                    Sort::BitVec(w) => Z3Term::V(BV::new_const(name, w)),
                    Sort::Array { .. } => {
                        return Err(SolverError::Unsupported(
                            "z3 oracle does not support array symbols".to_owned(),
                        ));
                    }
                    Sort::Int => {
                        return Err(SolverError::Unsupported(
                            "z3 oracle does not support integer symbols yet (ADR-0014)".to_owned(),
                        ));
                    }
                    Sort::Real => {
                        return Err(SolverError::Unsupported(
                            "z3 oracle does not support real symbols yet (ADR-0015)".to_owned(),
                        ));
                    }
                    Sort::Datatype(_) => {
                        return Err(SolverError::Unsupported(
                            "z3 oracle does not support datatype symbols yet (ADR-0022)".to_owned(),
                        ));
                    }
                };
                cache.insert(t, term);
            }
            TermNode::App { op, args } => {
                if matches!(
                    op,
                    Op::Apply(_)
                        | Op::IntNeg
                        | Op::IntAdd
                        | Op::IntSub
                        | Op::IntMul
                        | Op::IntDiv
                        | Op::IntMod
                        | Op::IntAbs
                        | Op::IntLt
                        | Op::IntLe
                        | Op::IntGt
                        | Op::IntGe
                        | Op::RealNeg
                        | Op::RealAdd
                        | Op::RealSub
                        | Op::RealMul
                        | Op::RealDiv
                        | Op::RealLt
                        | Op::RealLe
                        | Op::RealGt
                        | Op::RealGe
                        | Op::Forall(_)
                        | Op::Exists(_)
                        | Op::DtConstruct { .. }
                        | Op::DtSelect { .. }
                        | Op::DtTest(_)
                        | Op::ConstArray { .. }
                        | Op::IntToReal
                        | Op::RealToInt
                        | Op::RealIsInt
                        | Op::Bv2Nat
                        | Op::Int2Bv { .. }
                ) {
                    return Err(SolverError::Unsupported(
                        "z3 oracle does not support uninterpreted functions, integer/real \
                         arithmetic, datatypes, or quantifiers yet"
                            .to_owned(),
                    ));
                }
                if children_ready {
                    let translated = apply(*op, args, cache);
                    cache.insert(t, translated);
                } else {
                    stack.push((t, true));
                    for &a in &**args {
                        stack.push((a, false));
                    }
                }
            }
        }
    }
    Ok(cache[&root].clone())
}

fn bv_constant(width: u32, value: u128) -> Result<BV, SolverError> {
    if let Ok(v) = u64::try_from(value) {
        Ok(BV::from_u64(v, width))
    } else {
        BV::from_str(width, &value.to_string()).ok_or_else(|| {
            SolverError::Backend(format!("Z3 rejected wide constant {value} (width {width})"))
        })
    }
}

/// Applies an operator over already-translated children. Sort correctness
/// is guaranteed by the arena builders, so mismatches are unreachable.
fn apply(op: Op, args: &[TermId], cache: &HashMap<TermId, Z3Term>) -> Z3Term {
    let b = |i: usize| cache[&args[i]].as_bool();
    let v = |i: usize| cache[&args[i]].as_bv();
    match op {
        Op::BoolNot => Z3Term::B(b(0).not()),
        Op::BoolAnd => Z3Term::B(Bool::and(&[b(0).clone(), b(1).clone()])),
        Op::BoolOr => Z3Term::B(Bool::or(&[b(0).clone(), b(1).clone()])),
        Op::BoolXor => Z3Term::B(b(0).xor(b(1))),
        Op::BoolImplies => Z3Term::B(b(0).implies(b(1))),
        Op::BvNot => Z3Term::V(v(0).bvnot()),
        Op::BvAnd => Z3Term::V(v(0).bvand(v(1))),
        Op::BvOr => Z3Term::V(v(0).bvor(v(1))),
        Op::BvXor => Z3Term::V(v(0).bvxor(v(1))),
        Op::BvNand => Z3Term::V(v(0).bvnand(v(1))),
        Op::BvNor => Z3Term::V(v(0).bvnor(v(1))),
        Op::BvXnor => Z3Term::V(v(0).bvxnor(v(1))),
        Op::BvNeg => Z3Term::V(v(0).bvneg()),
        Op::BvAdd => Z3Term::V(v(0).bvadd(v(1))),
        Op::BvSub => Z3Term::V(v(0).bvsub(v(1))),
        Op::BvMul => Z3Term::V(v(0).bvmul(v(1))),
        Op::BvUdiv => Z3Term::V(v(0).bvudiv(v(1))),
        Op::BvUrem => Z3Term::V(v(0).bvurem(v(1))),
        Op::BvSdiv => Z3Term::V(v(0).bvsdiv(v(1))),
        Op::BvSrem => Z3Term::V(v(0).bvsrem(v(1))),
        Op::BvSmod => Z3Term::V(v(0).bvsmod(v(1))),
        Op::BvShl => Z3Term::V(v(0).bvshl(v(1))),
        Op::BvLshr => Z3Term::V(v(0).bvlshr(v(1))),
        Op::BvAshr => Z3Term::V(v(0).bvashr(v(1))),
        Op::BvUlt => Z3Term::B(v(0).bvult(v(1))),
        Op::BvUle => Z3Term::B(v(0).bvule(v(1))),
        Op::BvUgt => Z3Term::B(v(0).bvugt(v(1))),
        Op::BvUge => Z3Term::B(v(0).bvuge(v(1))),
        Op::BvSlt => Z3Term::B(v(0).bvslt(v(1))),
        Op::BvSle => Z3Term::B(v(0).bvsle(v(1))),
        Op::BvSgt => Z3Term::B(v(0).bvsgt(v(1))),
        Op::BvSge => Z3Term::B(v(0).bvsge(v(1))),
        Op::Eq => match (&cache[&args[0]], &cache[&args[1]]) {
            (Z3Term::B(x), Z3Term::B(y)) => Z3Term::B(x.eq(y)),
            (Z3Term::V(x), Z3Term::V(y)) => Z3Term::B(x.eq(y)),
            _ => unreachable!("builder-checked same-sort equality"),
        },
        Op::Ite => match (&cache[&args[1]], &cache[&args[2]]) {
            (Z3Term::B(x), Z3Term::B(y)) => Z3Term::B(b(0).ite(x, y)),
            (Z3Term::V(x), Z3Term::V(y)) => Z3Term::V(b(0).ite(x, y)),
            _ => unreachable!("builder-checked same-sort branches"),
        },
        // bvcomp as a derived form: ite(x = y, #b1, #b0).
        Op::BvComp => Z3Term::V(v(0).eq(v(1)).ite(&BV::from_u64(1, 1), &BV::from_u64(0, 1))),
        Op::Extract { hi, lo } => Z3Term::V(v(0).extract(hi, lo)),
        Op::Concat => Z3Term::V(v(0).concat(v(1))),
        Op::ZeroExt { by } => Z3Term::V(v(0).zero_ext(by)),
        Op::SignExt { by } => Z3Term::V(v(0).sign_ext(by)),
        // Rotates as derived extract/concat forms; builders normalized the
        // amount modulo width, so 0 <= by < width.
        Op::RotateLeft { by } => Z3Term::V(rotate_left(v(0), by)),
        Op::RotateRight { by } => {
            let w = v(0).get_size();
            Z3Term::V(rotate_left(v(0), (w - by) % w))
        }
        // Array, uninterpreted-function, integer, real, quantifier, and datatype
        // terms are rejected during translation before any select/store/apply/int/
        // datatype op is reached (ADR-0010, ADR-0013, ADR-0014, ADR-0022), so this
        // is unreachable.
        Op::Select
        | Op::Store
        | Op::Apply(_)
        | Op::IntNeg
        | Op::IntAdd
        | Op::IntSub
        | Op::IntMul
        | Op::IntDiv
        | Op::IntMod
        | Op::IntAbs
        | Op::IntLt
        | Op::IntLe
        | Op::IntGt
        | Op::IntGe
        | Op::RealNeg
        | Op::RealAdd
        | Op::RealSub
        | Op::RealMul
        | Op::RealDiv
        | Op::RealLt
        | Op::RealLe
        | Op::RealGt
        | Op::RealGe
        | Op::Forall(_)
        | Op::Exists(_)
        | Op::DtConstruct { .. }
        | Op::DtSelect { .. }
        | Op::DtTest(_)
        | Op::ConstArray { .. }
        | Op::IntToReal
        | Op::RealToInt
        | Op::RealIsInt
        | Op::Bv2Nat
        | Op::Int2Bv { .. } => {
            unreachable!(
                "array, UF, integer, real, quantifier, and datatype terms are rejected during z3 translation"
            )
        }
    }
}

/// Rotate left via extract/concat: `x[w-k-1:0] ++ x[w-1:w-k]`.
fn rotate_left(x: &BV, k: u32) -> BV {
    if k == 0 {
        return x.clone();
    }
    let w = x.get_size();
    x.extract(w - k - 1, 0).concat(x.extract(w - 1, w - k))
}
