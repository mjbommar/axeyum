//! C4.3 — build a [`ScalarLoopSystem`] from AST loop expressions, reusing the
//! real expression lowering ([`crate::lower::lower_pure_expr`]) per BMC step. This
//! wires the **scalar-loop fragment** of restricted-Rust to the warm
//! [`bounded_model_check`](axeyum_solver::bounded_model_check) route: deep loops
//! get warm-solver reuse across unroll depths instead of being unrolled into one
//! one-shot query.
//!
//! ## Soundness
//!
//! Each iteration's update uses wrapping BV arithmetic for the *term* value, while
//! the panic classes that arithmetic can hit (overflow, `÷0`/`%0`) are collected
//! into the **bad** predicate — so an overflowing update is caught as a bad state,
//! never silently wrapped past an assertion. The bad state is
//! `guard ∧ (¬assertᵢ ∨ update-panicⱼ)`: an in-loop assertion can only fail on an
//! iteration that actually runs (the guard holds).

use std::collections::HashMap;

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{SolverConfig, SolverError};

use crate::ast::{Expr, Program, Stmt, Ty};
use crate::bmc::{LoopSafety, ScalarLoopSystem, run_loop};
use crate::lower::lower_pure_expr;

/// An AST description of a scalar loop over uniform-width integer variables.
pub struct AstLoop {
    /// State variables in order: `(name, type)`. All must share one BV width.
    pub vars: Vec<(String, Ty)>,
    /// Initial value per variable, in `vars` order: `Some(c)` pins it to constant
    /// `c`; `None` leaves it an unconstrained symbolic input (e.g. a parameter).
    pub init: Vec<Option<u128>>,
    /// The loop guard — a `Bool` expression over the variables.
    pub guard: Expr,
    /// Per-variable next-value expressions, in `vars` order.
    pub updates: Vec<Expr>,
    /// Per-iteration assertion conditions; a bad state is reachable when one fails
    /// while the guard holds (or an update hits a panic class).
    pub asserts: Vec<Expr>,
}

fn env_of(vars: &[(String, Ty)], terms: &[TermId]) -> Vec<(String, TermId, Ty)> {
    vars.iter()
        .zip(terms)
        .map(|((n, t), &term)| (n.clone(), term, *t))
        .collect()
}

fn lower_err(e: &crate::lower::LowerError) -> SolverError {
    SolverError::Unsupported(format!("loop lowering: {e}"))
}

/// Builds a [`ScalarLoopSystem`] from an [`AstLoop`], or `None` if the variables
/// are not all the same integer width, or the `init`/`updates` arities are wrong
/// (the scalar-loop fragment requirements).
#[must_use]
pub fn loop_system(spec: AstLoop) -> Option<ScalarLoopSystem> {
    let AstLoop {
        vars,
        init: init_vals,
        guard: guard_expr,
        updates,
        asserts,
    } = spec;
    let width = match vars.first()?.1 {
        Ty::Int { width, .. } => width,
        Ty::Bool => return None,
    };
    let uniform = vars
        .iter()
        .all(|(_, ty)| matches!(ty, Ty::Int { width: w, .. } if *w == width));
    if !uniform || init_vals.len() != vars.len() || updates.len() != vars.len() {
        return None;
    }
    let names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();

    let init_fn = Box::new(
        move |arena: &mut TermArena, v: &[TermId]| -> Result<TermId, SolverError> {
            let mut acc: Option<TermId> = None;
            for (k, val) in init_vals.iter().enumerate() {
                let Some(c) = val else { continue };
                let lit = arena.bv_const(width, *c)?;
                let eq_k = arena.eq(v[k], lit)?;
                acc = Some(match acc {
                    None => eq_k,
                    Some(a) => arena.and(a, eq_k)?,
                });
            }
            // No pinned initial values → unconstrained start (all inputs free).
            match acc {
                Some(t) => Ok(t),
                None => Ok(arena.bool_const(true)),
            }
        },
    );

    let guard_vars = vars.clone();
    let guard_e = guard_expr.clone();
    let guard_fn = Box::new(
        move |arena: &mut TermArena, v: &[TermId]| -> Result<TermId, SolverError> {
            let env = env_of(&guard_vars, v);
            Ok(lower_pure_expr(arena, &env, &guard_e)
                .map_err(|e| lower_err(&e))?
                .term)
        },
    );

    let upd_vars = vars.clone();
    let upd_exprs = updates.clone();
    let update_fn = Box::new(
        move |arena: &mut TermArena, v: &[TermId]| -> Result<Vec<TermId>, SolverError> {
            let env = env_of(&upd_vars, v);
            let mut out = Vec::with_capacity(upd_exprs.len());
            for e in &upd_exprs {
                out.push(
                    lower_pure_expr(arena, &env, e)
                        .map_err(|e| lower_err(&e))?
                        .term,
                );
            }
            Ok(out)
        },
    );

    // The bad-state closure consumes the remaining moved locals.
    let bad_fn = Box::new(
        move |arena: &mut TermArena, v: &[TermId]| -> Result<TermId, SolverError> {
            let env = env_of(&vars, v);
            let guard_t = lower_pure_expr(arena, &env, &guard_expr)
                .map_err(|e| lower_err(&e))?
                .term;
            let mut disjunct: Option<TermId> = None;
            // Assertion violations.
            for a in &asserts {
                let cond = lower_pure_expr(arena, &env, a)
                    .map_err(|e| lower_err(&e))?
                    .term;
                let neg = arena.not(cond)?;
                disjunct = Some(match disjunct {
                    None => neg,
                    Some(d) => arena.or(d, neg)?,
                });
            }
            // Panic classes the updates themselves can hit (overflow, ÷0).
            for e in &updates {
                for (_, pred) in lower_pure_expr(arena, &env, e)
                    .map_err(|e| lower_err(&e))?
                    .bad_predicates
                {
                    disjunct = Some(match disjunct {
                        None => pred,
                        Some(d) => arena.or(d, pred)?,
                    });
                }
            }
            match disjunct {
                Some(d) => Ok(arena.and(guard_t, d)?),
                None => Ok(arena.bool_const(false)),
            }
        },
    );

    Some(ScalarLoopSystem::new(
        width, names, init_fn, guard_fn, update_fn, bad_fn,
    ))
}

/// Substitutes every `Var(n)` in `e` with `env[n]` (recursively), leaving names
/// not in `env` untouched — used to thread a loop body's sequential assignments
/// into each variable's end-of-iteration expression over the pre-state.
fn substitute(e: &Expr, env: &HashMap<String, Expr>) -> Expr {
    match e {
        Expr::Var(n) => env.get(n).cloned().unwrap_or_else(|| e.clone()),
        Expr::Binary { op, lhs, rhs } => Expr::Binary {
            op: *op,
            lhs: Box::new(substitute(lhs, env)),
            rhs: Box::new(substitute(rhs, env)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op: *op,
            operand: Box::new(substitute(operand, env)),
        },
        Expr::Ite { cond, then, els } => Expr::Ite {
            cond: Box::new(substitute(cond, env)),
            then: Box::new(substitute(then, env)),
            els: Box::new(substitute(els, env)),
        },
        Expr::Index { array, index, ty } => Expr::Index {
            array: array.clone(),
            index: Box::new(substitute(index, env)),
            ty: *ty,
        },
        Expr::UnwrapOption { is_some, value } => Expr::UnwrapOption {
            is_some: Box::new(substitute(is_some, env)),
            value: Box::new(substitute(value, env)),
        },
        Expr::IntLit { .. } | Expr::BoolLit(_) => e.clone(),
    }
}

/// Recognizes the `let* ; while { straight-line body }` shape of a `#[verify]`
/// [`Program`] and builds the equivalent [`AstLoop`] (C4.4): scalar params are
/// free initial state, pre-loop `let x = <const>` bindings are pinned initial
/// state, and the `while` body's sequential `Assign`/`Assert` statements thread
/// into per-variable update expressions and position-correct assertion conditions
/// via [`substitute`]. Returns `None` for anything outside this fragment (arrays,
/// nested control flow in the body, a non-constant `let`, …) — the caller then
/// falls back to the unroll route.
#[must_use]
pub fn loop_from_program(program: &Program) -> Option<AstLoop> {
    if !program.arrays.is_empty() {
        return None;
    }
    let (last, lets) = program.body.split_last()?;
    let Stmt::While { cond, body, .. } = last else {
        return None;
    };
    let mut vars: Vec<(String, Ty)> = Vec::new();
    let mut init: Vec<Option<u128>> = Vec::new();
    for p in &program.params {
        vars.push((p.name.clone(), p.ty));
        init.push(None);
    }
    for s in lets {
        let Stmt::Let { name, ty, value } = s else {
            return None;
        };
        let Expr::IntLit { value: c, .. } = value else {
            return None;
        };
        vars.push((name.clone(), *ty));
        init.push(Some(*c));
    }
    let mut current: HashMap<String, Expr> = vars
        .iter()
        .map(|(n, _)| (n.clone(), Expr::Var(n.clone())))
        .collect();
    let mut asserts: Vec<Expr> = Vec::new();
    for s in body {
        match s {
            Stmt::Assign { name, value } => {
                if !current.contains_key(name) {
                    return None;
                }
                let v = substitute(value, &current);
                current.insert(name.clone(), v);
            }
            Stmt::Assert(c) => asserts.push(substitute(c, &current)),
            // Nested control flow / non-straight-line statements fall back to
            // unrolling (a later C4 slice can fold `if` into guarded updates).
            _ => return None,
        }
    }
    let updates: Vec<Expr> = vars
        .iter()
        .map(|(n, _)| {
            current
                .get(n)
                .cloned()
                .unwrap_or_else(|| Expr::Var(n.clone()))
        })
        .collect();
    Some(AstLoop {
        vars,
        init,
        guard: cond.clone(),
        updates,
        asserts,
    })
}

/// Verifies a `#[verify]` loop [`Program`] via the **warm** BMC route when it is
/// in the [`loop_from_program`] fragment. Returns `None` (caller falls back to the
/// unroll route) otherwise.
///
/// # Errors
///
/// Propagates a hard solver failure; an undecided depth is [`LoopSafety::Unknown`].
pub fn check_program_loop(
    program: &Program,
    bound: usize,
    config: &SolverConfig,
) -> Option<Result<LoopSafety, SolverError>> {
    let spec = loop_from_program(program)?;
    let system = loop_system(spec)?;
    Some(run_loop(&system, bound, config))
}
