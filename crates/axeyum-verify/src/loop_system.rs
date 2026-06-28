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

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::SolverError;

use crate::ast::{Expr, Ty};
use crate::bmc::ScalarLoopSystem;
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
