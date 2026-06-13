//! Lazy SMT (DPLL(T)) over linear real arithmetic, **combined with the
//! bit-blasted theories** (ADR-0015 follow-on).
//!
//! [`check_with_lra_dpll`] decides an arbitrary Boolean combination of linear
//! real constraints **and** bit-vector / array / uninterpreted-function /
//! bounded-integer constraints in one query. Reals share no sort with those
//! theories, so the only coupling is propositional — making this lazy-SMT loop a
//! *complete* combination procedure (no interface-equality propagation needed).
//! Only the real atoms are abstracted to fresh Boolean propositions; every
//! non-real subterm is left intact for the bit-blasting composition
//! ([`crate::check_with_all_theories`]) to decide natively. It is the classic
//! lazy-SMT loop:
//!
//! 1. **Boolean abstraction.** Each distinct real order atom (`<`, `<=`, `>`,
//!    `>=`) is replaced by a fresh Boolean proposition, yielding a pure-Boolean
//!    skeleton over those propositions (and any original Boolean variables).
//! 2. **SAT.** The skeleton (plus learned blocking clauses) is solved by the
//!    pure-Rust [`SatBvBackend`]; a propositional model fixes each atom's truth.
//! 3. **Theory.** The chosen atom literals form a *conjunction*, decided by the
//!    exact-rational [`crate::check_with_lra`]. Theory-consistent → done; a
//!    theory conflict adds the blocking clause (the negation of the offending
//!    assignment) and the loop repeats.
//!
//! Termination is guaranteed: each round blocks at least one of the finitely
//! many atom assignments. **Trust:** a `sat` real model is replayed through the
//! ground evaluator against the *original* assertions, so neither the SAT search
//! nor the theory search can yield an unsound `sat`. Real **equality** atoms are
//! abstracted to `(a <= b) and (a >= b)`, so equality and **disequality** (the
//! negation `a < b or a > b`) are handled by the order-atom machinery and the
//! SAT case split.

use std::collections::HashMap;

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::combined::check_with_all_theories;
use crate::lia::DEFAULT_INT_WIDTH;
use crate::lra::{check_with_lra, lra_farkas_certificate};
use crate::model::Model;
use crate::sat_bv_backend::SatBvBackend;

/// A hard cap on lazy-SMT rounds, a backstop against a refinement bug (the loop
/// is otherwise bounded by the number of distinct atom assignments).
const MAX_ROUNDS: usize = 100_000;

/// Decides a Boolean combination of linear real order constraints by lazy SMT.
///
/// The returned [`Model`] carries real variable values (and original Boolean
/// variable values) and replays against the original assertions.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion is outside Boolean
/// structure over real order atoms (e.g. a real equality atom, or a non-real
/// arithmetic atom), or [`SolverError`] from the underlying SAT backend; a
/// `sat` model that fails to replay is a [`SolverError::Backend`].
pub fn check_with_lra_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // 1. Boolean abstraction: skeleton terms + the atom map.
    let mut ctx = Abstractor::default();
    let mut skeleton = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        skeleton.push(ctx.abstract_term(arena, assertion)?);
    }

    let mut backend = SatBvBackend::new();
    let mut blocking: Vec<TermId> = Vec::new();

    for _ in 0..MAX_ROUNDS {
        // 2. Decide the skeleton (real atoms abstracted to props; every other
        //    theory — bit-vectors, arrays, functions, bounded integers — left
        //    intact) plus learned blocking clauses, with the full bit-blasting
        //    composition. Reals share no sort with those theories, so the only
        //    coupling is propositional and this loop is a complete combination.
        let mut sat_assertions = skeleton.clone();
        sat_assertions.extend(blocking.iter().copied());
        let propositional = match check_with_all_theories(
            &mut backend,
            arena,
            &sat_assertions,
            DEFAULT_INT_WIDTH,
            config,
        )? {
            CheckResult::Sat(model) => model,
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
        };

        // 3. Read each atom's truth and form the theory conjunction.
        let mut theory_lits = Vec::with_capacity(ctx.atoms.len());
        let mut assignment: Vec<(SymbolId, bool)> = Vec::with_capacity(ctx.atoms.len());
        for atom in &ctx.atoms {
            let truth = propositional
                .get(atom.prop)
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            assignment.push((atom.prop, truth));
            theory_lits.push(if truth {
                atom.term
            } else {
                arena.not(atom.term)?
            });
        }

        match check_with_lra(arena, &theory_lits)? {
            CheckResult::Sat(theory_model) => {
                return finish_sat(arena, assertions, &ctx, &propositional, &theory_model);
            }
            CheckResult::Unsat => {
                // Theory conflict: block this atom assignment and retry. The
                // Farkas certificate names the infeasible core — the atoms with a
                // nonzero multiplier — so block only those (a sound, strictly
                // stronger clause that rules out every assignment sharing the
                // core, not just this one). `theory_lits`, `assignment`, and the
                // certificate atoms are all in `ctx.atoms` order, so multiplier
                // index `i` is `assignment[i]`.
                let core = conflict_core(arena, &theory_lits, &assignment)?;
                blocking.push(block_clause(arena, &core)?);
            }
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
        }
    }

    Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("lazy SMT exceeded {MAX_ROUNDS} refinement rounds"),
    }))
}

/// Builds the final `sat` model (real values + original Boolean values) and
/// replays it against the original assertions.
fn finish_sat(
    arena: &TermArena,
    assertions: &[TermId],
    ctx: &Abstractor,
    propositional: &Model,
    theory_model: &Model,
) -> Result<CheckResult, SolverError> {
    let mut assignment = Assignment::new();
    let mut model = Model::new();
    // Real variable values from the theory solver.
    for (symbol, value) in theory_model.iter() {
        assignment.set(symbol, value.clone());
        model.set(symbol, value);
    }
    // Everything else from the bit-blasting model (Booleans, bit-vectors,
    // integers, arrays, functions). Skip the fresh atom propositions, and skip
    // real values — the backend default-completes real symbols to `Real(0)`,
    // which must not overwrite the theory solver's real assignment.
    for (symbol, value) in propositional.iter() {
        if ctx.is_atom_prop(symbol) || matches!(value, Value::Real(_)) {
            continue;
        }
        assignment.set(symbol, value.clone());
        model.set(symbol, value);
    }
    for (func, interp) in propositional.functions() {
        assignment.set_function(func, interp.clone());
        model.set_function(func, interp.clone());
    }

    for &assertion in assertions {
        match eval(arena, assertion, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(_) => {
                return Err(SolverError::Backend(format!(
                    "lazy-SMT sat model replay failed: assertion #{} not satisfied",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "lazy-SMT sat model replay failed: assertion #{} evaluation error: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(CheckResult::Sat(model))
}

/// Builds the blocking clause that rules out the current atom assignment: the
/// disjunction of each proposition's complement.
fn block_clause(
    arena: &mut TermArena,
    assignment: &[(SymbolId, bool)],
) -> Result<TermId, SolverError> {
    let mut clause: Option<TermId> = None;
    for &(prop, truth) in assignment {
        let var = arena.var(prop);
        let literal = if truth { arena.not(var)? } else { var };
        clause = Some(match clause {
            Some(acc) => arena.or(acc, literal)?,
            None => literal,
        });
    }
    // A non-empty assignment always yields a clause; an empty one (no atoms)
    // cannot reach here because a theory conflict implies at least one atom.
    clause.ok_or_else(|| SolverError::Backend("empty theory conflict".to_owned()))
}

/// Returns the sub-assignment forming the infeasible core of a theory conflict.
///
/// The Farkas certificate's nonzero-multiplier atoms are exactly the literals
/// that participate in the refutation, so blocking only those is sound (that
/// subset is genuinely infeasible) and strictly stronger than blocking the whole
/// assignment. Falls back to the full assignment when no certificate is
/// available or its shape does not line up one-to-one with the literals — still
/// sound, since a larger blocking clause only rules out fewer assignments.
fn conflict_core(
    arena: &TermArena,
    theory_lits: &[TermId],
    assignment: &[(SymbolId, bool)],
) -> Result<Vec<(SymbolId, bool)>, SolverError> {
    if let Some(certificate) = lra_farkas_certificate(arena, theory_lits)? {
        if certificate.multipliers.len() == assignment.len() {
            let core: Vec<(SymbolId, bool)> = assignment
                .iter()
                .zip(&certificate.multipliers)
                .filter(|(_, multiplier)| !multiplier.is_zero())
                .map(|(entry, _)| *entry)
                .collect();
            if !core.is_empty() {
                return Ok(core);
            }
        }
    }
    Ok(assignment.to_vec())
}

/// Whether `term` contains any real-sorted subterm.
fn contains_real(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if arena.sort_of(t) == Sort::Real {
            return true;
        }
        if let TermNode::App { args, .. } = arena.node(t) {
            stack.extend(args.iter().copied());
        }
    }
    false
}

/// One abstracted real atom: its fresh Boolean proposition and the original
/// comparison term.
struct AtomBinding {
    prop: SymbolId,
    term: TermId,
}

#[derive(Default)]
struct Abstractor {
    /// Maps an original atom term to its fresh proposition.
    atom_of: HashMap<TermId, SymbolId>,
    /// Maps a fresh proposition back, to filter it from the final model.
    props: std::collections::HashSet<SymbolId>,
    atoms: Vec<AtomBinding>,
    fresh_counter: usize,
}

impl Abstractor {
    fn is_atom_prop(&self, symbol: SymbolId) -> bool {
        self.props.contains(&symbol)
    }

    /// Rewrites an assertion into a skeleton: real atoms become fresh Boolean
    /// propositions, while every subterm that contains no real (bit-vectors,
    /// arrays, functions, integers, and the Boolean structure over them) is left
    /// intact for the bit-blasting backend to decide natively.
    fn abstract_term(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
    ) -> Result<TermId, SolverError> {
        // No real subterm: leave it for the bit-blasting composition.
        if !contains_real(arena, term) {
            return Ok(term);
        }
        let node = arena.node(term).clone();
        match node {
            TermNode::BoolConst(_) | TermNode::Symbol(_) => Ok(term),
            TermNode::App { op, args } => match op {
                Op::BoolNot => {
                    let a = self.abstract_term(arena, args[0])?;
                    Ok(arena.not(a)?)
                }
                Op::BoolAnd => self.rebuild_binary(arena, &args, TermArena::and),
                Op::BoolOr => self.rebuild_binary(arena, &args, TermArena::or),
                Op::BoolXor => self.rebuild_binary(arena, &args, TermArena::xor),
                Op::BoolImplies => self.rebuild_binary(arena, &args, TermArena::implies),
                // Boolean `=` (iff) and `ite` keep their structure when their
                // operands are Boolean; otherwise they are not a skeleton.
                Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                    self.rebuild_binary(arena, &args, TermArena::eq)
                }
                Op::Ite if arena.sort_of(term) == Sort::Bool => {
                    let c = self.abstract_term(arena, args[0])?;
                    let t = self.abstract_term(arena, args[1])?;
                    let e = self.abstract_term(arena, args[2])?;
                    Ok(arena.ite(c, t, e)?)
                }
                Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe => {
                    let prop = self.atom(arena, term);
                    Ok(arena.var(prop))
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Real => {
                    // Real equality `a = b` abstracts to `(a <= b) and (a >= b)`,
                    // so equality *and* disequality (its negation, `a < b or
                    // a > b`) flow through the order-atom machinery and the SAT
                    // case split — no special disequality reasoning in the theory
                    // solver.
                    let le = arena.real_le(args[0], args[1])?;
                    let ge = arena.real_ge(args[0], args[1])?;
                    let le_prop = self.abstract_term(arena, le)?;
                    let ge_prop = self.abstract_term(arena, ge)?;
                    Ok(arena.and(le_prop, ge_prop)?)
                }
                _ => Err(SolverError::Unsupported(
                    "lazy SMT: assertion is not Boolean structure over real order atoms".to_owned(),
                )),
            },
            TermNode::BvConst { .. } | TermNode::IntConst(_) | TermNode::RealConst(_) => {
                Err(SolverError::Unsupported(
                    "lazy SMT: non-Boolean constant at a Boolean position".to_owned(),
                ))
            }
        }
    }

    fn rebuild_binary(
        &mut self,
        arena: &mut TermArena,
        args: &[TermId],
        build: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
    ) -> Result<TermId, SolverError> {
        let a = self.abstract_term(arena, args[0])?;
        let b = self.abstract_term(arena, args[1])?;
        Ok(build(arena, a, b)?)
    }

    /// Returns the fresh proposition for an atom term, creating it once.
    fn atom(&mut self, arena: &mut TermArena, term: TermId) -> SymbolId {
        if let Some(&prop) = self.atom_of.get(&term) {
            return prop;
        }
        let name = format!("!lra_atom_{}", self.fresh_counter);
        self.fresh_counter += 1;
        let prop = arena
            .declare(&name, Sort::Bool)
            .expect("fresh Boolean proposition declares");
        self.atom_of.insert(term, prop);
        self.props.insert(prop);
        self.atoms.push(AtomBinding { prop, term });
        prop
    }
}
