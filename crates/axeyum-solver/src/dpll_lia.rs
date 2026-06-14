//! Boolean-structured `QF_LIA` by lazy-SMT / DPLL(T) over the integer simplex.
//!
//! The conjunctive integer decision procedure ([`crate::check_with_lia_simplex`],
//! ADR-0020) decides a *conjunction* of linear integer constraints. This module
//! lifts it to **arbitrary Boolean structure** — disjunctions, implications,
//! negations of integer atoms (e.g. `x <= 0 OR x >= 10`) — by the standard
//! lazy-SMT loop, mirroring [`crate::check_with_lra_dpll`] for integers:
//!
//! 1. **Abstract** every integer order atom to a fresh Boolean proposition and
//!    every integer equality `a = b` to `(a <= b) AND (a >= b)`, leaving the
//!    Boolean structure (and original Boolean variables) intact. The result is a
//!    propositional skeleton.
//! 2. **Decide the skeleton** (pure Boolean) to get a truth assignment to the
//!    atom propositions.
//! 3. **Theory-check** the implied conjunction of integer order literals with the
//!    simplex branch-and-bound. `sat` ⇒ build and replay a model; `unsat` ⇒ add a
//!    blocking clause ruling out this propositional assignment and retry.
//!
//! Soundness: every integer model of the original induces a skeleton-satisfying
//! truth assignment; the loop only returns `sat` after replaying the original
//! assertions, and only returns `unsat` when the skeleton plus learned blocking
//! clauses is propositionally unsatisfiable — i.e. no truth assignment is
//! theory-consistent. A round budget bounds the search (`unknown`, never wrong).
//! Equality is split into order atoms, so the theory solver never sees a
//! disequality.

use std::collections::HashMap;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{
    CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
};
use crate::lra::check_with_lia_simplex;
use crate::model::Model;
use crate::sat_bv_backend::SatBvBackend;

const ATOM_PREFIX: &str = "!lia_atom_";
const MAX_DPLL_ROUNDS: usize = 10_000;

/// Decides a Boolean-structured `QF_LIA` query by lazy-SMT over the simplex.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion is not Boolean structure
/// over linear-integer atoms (e.g. it mentions bit-vectors, arrays, or reals), so
/// the caller can fall back; or [`SolverError::Backend`] on a replay alarm.
pub fn check_with_lia_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut ctx = IntAbstractor::default();
    let mut skeleton = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        skeleton.push(ctx.abstract_term(arena, assertion)?);
    }

    let mut backend = SatBvBackend::new();
    let mut blocking: Vec<TermId> = Vec::new();

    for _ in 0..MAX_DPLL_ROUNDS {
        let mut sat_assertions = skeleton.clone();
        sat_assertions.extend(blocking.iter().copied());
        let propositional = match backend.check(arena, &sat_assertions, config)? {
            CheckResult::Sat(model) => model,
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
        };

        // The integer literals implied by this propositional assignment.
        let mut theory_lits = Vec::with_capacity(ctx.atoms.len());
        let mut truths = Vec::with_capacity(ctx.atoms.len());
        for atom in &ctx.atoms {
            let truth = propositional
                .get(atom.prop)
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            truths.push(truth);
            theory_lits.push(if truth {
                atom.term
            } else {
                arena.not(atom.term)?
            });
        }

        match check_with_lia_simplex(arena, &theory_lits)? {
            CheckResult::Sat(theory_model) => {
                return finish_sat(arena, assertions, &ctx, &propositional, &theory_model);
            }
            CheckResult::Unsat => {
                // Minimize the conflict to a small unsatisfiable core, then block
                // only that core — a strictly stronger lemma that rules out every
                // assignment sharing it, not just this one, so the loop converges
                // in far fewer rounds on disjunction-heavy queries.
                let core = minimize_core(arena, &theory_lits)?;
                blocking.push(block_clause(arena, &ctx.atoms, &truths, &core)?);
            }
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
        }
    }

    Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("lazy QF_LIA exceeded {MAX_DPLL_ROUNDS} refinement rounds"),
    }))
}

/// Builds the model from the propositional (Boolean) and integer theory models
/// and replays the original assertions.
fn finish_sat(
    arena: &TermArena,
    assertions: &[TermId],
    ctx: &IntAbstractor,
    propositional: &Model,
    theory_model: &Model,
) -> Result<CheckResult, SolverError> {
    let mut model = Model::new();
    let mut assignment = axeyum_ir::Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        if ctx.is_atom_prop(symbol) || name.starts_with(ATOM_PREFIX) {
            continue;
        }
        let value = match sort {
            Sort::Int => theory_model.get(symbol),
            Sort::Bool => propositional.get(symbol),
            _ => None,
        };
        if let Some(value) = value {
            model.set(symbol, value.clone());
            assignment.set(symbol, value);
        }
    }
    for &assertion in assertions {
        match eval(arena, assertion, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(_) => {
                return Err(SolverError::Backend(format!(
                    "lia dpll sat model replay failed: assertion #{} not satisfied",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "lia dpll sat model replay error on assertion #{}: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(CheckResult::Sat(model))
}

/// Deletion-based minimization of a theory conflict: returns the indices (into
/// `theory_lits`) of a subset that is still unsatisfiable but minimal — dropping
/// any member makes it satisfiable (or undecided, conservatively kept). Each
/// surviving member is necessary, so the negated core is a strong, sound lemma.
fn minimize_core(arena: &TermArena, theory_lits: &[TermId]) -> Result<Vec<usize>, SolverError> {
    let mut core: Vec<usize> = (0..theory_lits.len()).collect();
    for candidate in 0..theory_lits.len() {
        if !core.contains(&candidate) {
            continue;
        }
        let trial: Vec<TermId> = core
            .iter()
            .filter(|&&i| i != candidate)
            .map(|&i| theory_lits[i])
            .collect();
        // Drop the candidate only if the remainder is *definitively* unsat.
        if !trial.is_empty() && matches!(check_with_lia_simplex(arena, &trial)?, CheckResult::Unsat)
        {
            core.retain(|&i| i != candidate);
        }
    }
    Ok(core)
}

/// A clause forcing at least one atom in `core` to flip from `truths`. `core`
/// indexes `atoms`/`truths` (same order as the theory literals).
fn block_clause(
    arena: &mut TermArena,
    atoms: &[IntAtom],
    truths: &[bool],
    core: &[usize],
) -> Result<TermId, SolverError> {
    let mut clause: Option<TermId> = None;
    for &i in core {
        let prop = arena.var(atoms[i].prop);
        let lit = if truths[i] { arena.not(prop)? } else { prop };
        clause = Some(match clause {
            None => lit,
            Some(acc) => arena.or(acc, lit)?,
        });
    }
    // A non-empty conflict always yields a non-empty core.
    clause.ok_or_else(|| SolverError::Backend("lia dpll: empty conflict clause".to_string()))
}

/// One abstracted integer order atom and its fresh proposition.
struct IntAtom {
    prop: SymbolId,
    term: TermId,
}

/// Abstracts Boolean structure over integer atoms into a propositional skeleton.
#[derive(Default)]
struct IntAbstractor {
    atom_of: HashMap<TermId, SymbolId>,
    props: std::collections::HashSet<SymbolId>,
    atoms: Vec<IntAtom>,
    fresh_counter: usize,
}

impl IntAbstractor {
    fn is_atom_prop(&self, symbol: SymbolId) -> bool {
        self.props.contains(&symbol)
    }

    fn abstract_term(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
    ) -> Result<TermId, SolverError> {
        let node = arena.node(term).clone();
        match node {
            TermNode::BoolConst(_) => Ok(term),
            // An original Boolean variable; keep it in the skeleton.
            TermNode::Symbol(_) if arena.sort_of(term) == Sort::Bool => Ok(term),
            TermNode::App { op, args } => match op {
                Op::BoolNot => {
                    let a = self.abstract_term(arena, args[0])?;
                    Ok(arena.not(a)?)
                }
                Op::BoolAnd => self.rebuild(arena, &args, TermArena::and),
                Op::BoolOr => self.rebuild(arena, &args, TermArena::or),
                Op::BoolXor => self.rebuild(arena, &args, TermArena::xor),
                Op::BoolImplies => self.rebuild(arena, &args, TermArena::implies),
                Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                    self.rebuild(arena, &args, TermArena::eq)
                }
                Op::Ite if arena.sort_of(term) == Sort::Bool => {
                    let c = self.abstract_term(arena, args[0])?;
                    let t = self.abstract_term(arena, args[1])?;
                    let e = self.abstract_term(arena, args[2])?;
                    Ok(arena.ite(c, t, e)?)
                }
                Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe => {
                    let prop = self.atom(arena, term);
                    Ok(arena.var(prop))
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Int => {
                    // a = b  ->  (a <= b) AND (a >= b), so equality and its
                    // negation both flow through order atoms; the theory solver
                    // never sees a disequality.
                    let le = arena.int_le(args[0], args[1])?;
                    let ge = arena.int_ge(args[0], args[1])?;
                    let le_prop = self.abstract_term(arena, le)?;
                    let ge_prop = self.abstract_term(arena, ge)?;
                    Ok(arena.and(le_prop, ge_prop)?)
                }
                _ => Err(SolverError::Unsupported(
                    "lazy QF_LIA: assertion is not Boolean structure over integer atoms".to_owned(),
                )),
            },
            _ => Err(SolverError::Unsupported(
                "lazy QF_LIA: non-Boolean, non-integer-atom term in a Boolean position".to_owned(),
            )),
        }
    }

    fn rebuild(
        &mut self,
        arena: &mut TermArena,
        args: &[TermId],
        build: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
    ) -> Result<TermId, SolverError> {
        let a = self.abstract_term(arena, args[0])?;
        let b = self.abstract_term(arena, args[1])?;
        Ok(build(arena, a, b)?)
    }

    fn atom(&mut self, arena: &mut TermArena, term: TermId) -> SymbolId {
        if let Some(&prop) = self.atom_of.get(&term) {
            return prop;
        }
        let name = format!("{ATOM_PREFIX}{}", self.fresh_counter);
        self.fresh_counter += 1;
        let prop = arena
            .declare(&name, Sort::Bool)
            .expect("fresh Boolean proposition declares");
        self.atom_of.insert(term, prop);
        self.props.insert(prop);
        self.atoms.push(IntAtom { prop, term });
        prop
    }
}
