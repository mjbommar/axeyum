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

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode, Value};
use z3::ast::{BV, Bool};
use z3::{Config, SatResult, Solver, with_z3_config};

use crate::backend::{Capabilities, CheckResult, SolverBackend, SolverConfig, SolverError};
use crate::model::Model;

/// Z3 oracle backend. Stateless in M0; each `check` is one-shot.
#[derive(Debug, Default)]
pub struct Z3Backend {}

impl Z3Backend {
    /// Creates a new backend instance.
    pub fn new() -> Self {
        Self {}
    }
}

impl SolverBackend for Z3Backend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "z3".to_owned(),
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
        for &t in assertions {
            if arena.sort_of(t) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(t));
            }
        }
        let mut cfg = Config::new();
        cfg.set_model_generation(true);
        if let Some(timeout) = config.timeout {
            cfg.set_timeout_msec(u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX));
        }
        // The closure runs against a scoped thread-local Z3 context; no Z3
        // object survives past it.
        with_z3_config(&cfg, || run_check(arena, assertions))
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

fn run_check(arena: &TermArena, assertions: &[TermId]) -> Result<CheckResult, SolverError> {
    let mut cache: HashMap<TermId, Z3Term> = HashMap::new();
    let solver = Solver::new();
    for &t in assertions {
        let translated = translate(arena, t, &mut cache)?;
        solver.assert(translated.as_bool());
    }
    match solver.check() {
        SatResult::Unsat => Ok(CheckResult::Unsat),
        SatResult::Unknown => Ok(CheckResult::Unknown(
            solver
                .get_reason_unknown()
                .unwrap_or_else(|| "unknown".to_owned()),
        )),
        SatResult::Sat => {
            let z3_model = solver
                .get_model()
                .ok_or_else(|| SolverError::Backend("sat result without model".to_owned()))?;
            let mut model = Model::new();
            for (sym, name, sort) in arena.symbols() {
                let value = match sort {
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
            Ok(CheckResult::Sat(model))
        }
    }
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
            TermNode::Symbol(s) => {
                let (name, sort) = arena.symbol(*s);
                let term = match sort {
                    Sort::Bool => Z3Term::B(Bool::new_const(name)),
                    Sort::BitVec(w) => Z3Term::V(BV::new_const(name, w)),
                };
                cache.insert(t, term);
            }
            TermNode::App { op, args } => {
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
        Op::BvNot => Z3Term::V(v(0).bvnot()),
        Op::BvAnd => Z3Term::V(v(0).bvand(v(1))),
        Op::BvOr => Z3Term::V(v(0).bvor(v(1))),
        Op::BvXor => Z3Term::V(v(0).bvxor(v(1))),
        Op::BvAdd => Z3Term::V(v(0).bvadd(v(1))),
        Op::BvUlt => Z3Term::B(v(0).bvult(v(1))),
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
        Op::Extract { hi, lo } => Z3Term::V(v(0).extract(hi, lo)),
        Op::Concat => Z3Term::V(v(0).concat(v(1))),
    }
}
