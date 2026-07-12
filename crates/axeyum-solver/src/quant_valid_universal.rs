//! Valid-universal elimination (sat-side universal-closure validity check).
//!
//! The finite-domain quantifier path ([`crate::check_with_quantifiers`]) is
//! complete for `Bool`/`BitVec` bound variables, and the infinite-domain
//! fallback ([`crate::prove_unsat_by_instantiation`] / MBQI) can only ever
//! conclude `unsat` or `unknown` — it has no *sat-side* decision. So a
//! standalone **valid** universal over `Int`/`Real`/an uninterpreted sort —
//! e.g. `∀x:Int. x + 0 == x`, `∀x. f(x) == f(x)`, `∀x:Real. x*x >= 0` — comes
//! back `unknown` even though it is satisfiable (true in *every* model).
//!
//! This pass closes that gap with the **universal-closure validity check**:
//!
//! > A top-level universally-quantified assertion `∀x. body(x)` is **valid**
//! > (true in every model — hence the assertion is satisfiable) **iff**
//! > `¬body[x := c]` is **UNSAT**, for a fresh uninterpreted constant `c` of
//! > `x`'s sort.
//!
//! *Soundness.* `c` is a fresh, otherwise-unconstrained constant, so it ranges
//! over every element of the sort across models. No model falsifies `body(c)`
//! ⟺ `body` holds for all `x` in all models ⟺ the universal is valid. A valid
//! universal is `true` in every model, so replacing the assertion with `true`
//! is **exact** (changes no model). When the body is quantifier-free, `¬body(c)`
//! is quantifier-free, so the existing QF deciders ([`crate::check_auto`])
//! decide it — and they already prove `c*c < 0` UNSAT (NRA sign rule),
//! `c + 0 != c` UNSAT (LIA), `f(c) != f(c)` UNSAT (EUF).
//!
//! The pass is **strictly additive**: a universal it *cannot prove valid* is
//! left untouched (it falls through to the existing instantiation/MBQI path),
//! so the problem is never weakened. Only an otherwise-`unknown` verdict can
//! become decided.
//!
//! *Termination.* The validity sub-check first dispatches to the
//! quantifier-free decider [`crate::check_auto`] on the (quantifier-free)
//! negated body. That decider never re-enters the quantifier front door, and
//! bodies that still contain a nested quantifier are skipped, so there is
//! exactly one bounded QF solve per candidate universal and no recursion. If
//! that route returns `unknown`, the proof-producing `QF_BV` exporter gets one
//! bounded second chance on the same sub-query, then a lazy-BV retry, and
//! finally a hardened qf-BV retry (native CDCL + CNF inprocessing) gets one
//! last bounded attempt before the universal is left untouched.

use std::collections::HashMap;
use std::time::Instant;

use axeyum_ir::{Op, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::proof::{UnsatProofOutcome, export_qf_bv_unsat_proof_within};

/// Rewrites every top-level universal `∀x. body` whose body is quantifier-free
/// and which this pass can **prove valid** into the trivially-true constant
/// `true`, leaving every other assertion unchanged.
///
/// A universal is proven valid when `¬body[x := c]` is *definitively* `unsat`
/// for a fresh uninterpreted constant `c` (see the module docs). A universal
/// whose validity sub-check returns `sat`/`unknown`, or whose body carries a
/// nested quantifier, is passed through untouched — so the caller may continue
/// to the existing instantiation/MBQI path for it.
///
/// Returns the (possibly) rewritten assertions and whether any universal was
/// eliminated. The rewrite is exact (a valid universal is `true` in every
/// model), so the caller may trust both `sat` and `unsat` of the result.
///
/// # Errors
///
/// Returns [`SolverError`] only from an internal IR builder failure or the QF
/// validity sub-solve; a sub-check that cannot decide is *not* an error — the
/// assertion is simply passed through unchanged.
pub fn eliminate_valid_universals(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<(Vec<TermId>, bool), SolverError> {
    let mut out = Vec::with_capacity(assertions.len());
    let mut rewrote = false;
    let mut fresh = 0u32;
    for &assertion in assertions {
        match try_eliminate(arena, assertion, config, &mut fresh)? {
            Some(simplified) => {
                rewrote = true;
                out.push(simplified);
            }
            None => out.push(assertion),
        }
    }
    Ok((out, rewrote))
}

/// Attempts the valid-universal rewrite on a single top-level assertion.
///
/// Returns `Ok(Some(true))` when the assertion is a (possibly nested) universal
/// prefix `∀x₁.…∀xₙ. body` with a quantifier-free `body` that is **proven valid**
/// (so the caller substitutes the trivially-true constant); `Ok(None)` otherwise
/// (not a universal, an innermost body that still carries a quantifier, or a
/// sub-check that did not establish validity), in which case the assertion is left
/// unchanged.
///
/// A *prefix* of `∀` binders is peeled — `∀x.∀y. body` is valid iff
/// `¬body[x:=cx, y:=cy]` is unsat for fresh constants `cx`, `cy` — so a flattened
/// multi-variable universal is handled in one sound QF sub-check.
fn try_eliminate(
    arena: &mut TermArena,
    assertion: TermId,
    config: &SolverConfig,
    fresh: &mut u32,
) -> Result<Option<TermId>, SolverError> {
    // Peel the leading `∀` prefix into its bound variables, with the innermost
    // body. (`∀x.∀y. body` ⇒ vars = [x, y], body.)
    let mut vars: Vec<axeyum_ir::SymbolId> = Vec::new();
    let mut body = assertion;
    while let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(body)
    {
        vars.push(*var);
        body = args[0];
    }
    if vars.is_empty() {
        return Ok(None); // not a universal
    }

    // The innermost body must be quantifier-free: a remaining quantifier (an `∃`,
    // or a `∀` not in the prefix) would make the validity sub-check itself
    // quantified. Leave such assertions for the existing quantifier path.
    if contains_quantifier(arena, body) {
        return Ok(None);
    }

    // Mint a *fresh* uninterpreted constant for each prefix variable (reserved
    // `!vu_*` prefix + per-pass counter, so no collision with a user/Skolem
    // symbol). Each constant is otherwise unconstrained — an arbitrary
    // representative of its sort — so `¬body` over them being unsat means `body`
    // holds for *all* values of the bound variables.
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    for &var in &vars {
        let sort = arena.symbol(var).1;
        let name = format!("!vu_{fresh}");
        *fresh += 1;
        let constant = arena.declare_internal(&name, sort).map_err(err)?;
        replacements.insert(arena.var(var), arena.var(constant));
    }

    // Form `body[xᵢ := cᵢ]` (all substitutions at once; capture-free since the
    // `cᵢ` are fresh and the `xᵢ` are distinct symbols).
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let instance = replace_subterms(arena, body, &replacements, &mut memo).map_err(err)?;

    // The negated body is the validity witness: the universal is valid iff this is
    // unsatisfiable.
    let negated = arena.not(instance).map_err(err)?;

    // Decide `¬body(c⃗)` with the *quantifier-free* dispatch. It carries no
    // quantifier (the body was QF and each `cᵢ` is a plain constant), so
    // `check_auto` cannot re-enter the quantifier front door — guaranteeing
    // termination with a single bounded QF solve. We pass the sub-query alone
    // (the only thing whose validity we are testing); other assertions never
    // constrain the `cᵢ`, so including them could only mask validity, not
    // create it. If that route declines, the proof-producing `QF_BV` exporter
    // gets one bounded second chance on the same sub-query, then lazy-BV gets a
    // bounded attempt, and finally a hardened qf-BV retry (native CDCL + CNF
    // inprocessing) gets one last bounded attempt.
    let qf_start = Instant::now();
    match check_auto(arena, &[negated], config) {
        Ok(CheckResult::Unsat) => Ok(Some(arena.bool_const(true))),
        Ok(CheckResult::Sat(_)) => Ok(None),
        Ok(CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            let deadline = config
                .timeout
                .and_then(|timeout| qf_start.checked_add(timeout));
            match export_qf_bv_unsat_proof_within(arena, &[negated], deadline) {
                Ok(UnsatProofOutcome::Proved(_)) => Ok(Some(arena.bool_const(true))),
                Ok(UnsatProofOutcome::Satisfiable | UnsatProofOutcome::Inconclusive)
                | Err(SolverError::Unsupported(_)) => {
                    let Some(remaining) = deadline
                        .map(|end| end.saturating_duration_since(Instant::now()))
                        .filter(|remaining| !remaining.is_zero())
                    else {
                        return Ok(None);
                    };
                    let mut lazy = config.clone().with_timeout(remaining);
                    lazy = lazy.with_lazy_bv(true).with_lazy_bv_abstract_ite(true);
                    match check_auto(arena, &[negated], &lazy) {
                        Ok(CheckResult::Unsat) => return Ok(Some(arena.bool_const(true))),
                        Ok(CheckResult::Sat(_)) | Ok(CheckResult::Unknown(_)) => {}
                        Err(SolverError::Unsupported(_)) => {}
                        Err(error) => return Err(error),
                    }
                    let Some(remaining) = deadline
                        .map(|end| end.saturating_duration_since(Instant::now()))
                        .filter(|remaining| !remaining.is_zero())
                    else {
                        return Ok(None);
                    };
                    let mut hardened = config.clone().with_timeout(remaining);
                    hardened.native_cdcl = true;
                    hardened.prove_unsat = true;
                    hardened.cnf_inprocessing = true;
                    hardened.cnf_vivify = true;
                    match check_auto(arena, &[negated], &hardened) {
                        Ok(CheckResult::Unsat) => Ok(Some(arena.bool_const(true))),
                        Ok(CheckResult::Sat(_)) | Ok(CheckResult::Unknown(_)) => Ok(None),
                        Err(SolverError::Unsupported(_)) => Ok(None),
                        Err(error) => Err(error),
                    }
                }
                Err(error) => Err(error),
            }
        }
        Err(error) => Err(error),
    }
}

/// Whether `term` contains any quantifier operator.
fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}
