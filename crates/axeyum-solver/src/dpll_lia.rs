//! Boolean-structured linear arithmetic (`QF_LIA`, `QF_LRA`, and their
//! combination `QF_LIRA`) by lazy-SMT / DPLL(T) over the exact-rational
//! simplices.
//!
//! The conjunctive procedures decide a *conjunction* of linear constraints —
//! [`crate::check_with_lia_simplex`] for integers (ADR-0020),
//! [`crate::check_with_lra`] for reals (ADR-0015). This module lifts them to
//! **arbitrary Boolean structure** (disjunctions, implications, negations of
//! arithmetic atoms, over both sorts at once):
//!
//! 1. **Abstract** every linear-arithmetic order atom to a fresh Boolean
//!    proposition (equality `a = b` split to `(a <= b) AND (a >= b)`), tagging
//!    each by its theory (`Int`/`Real`), and keep the Boolean structure.
//! 2. **Decide the skeleton** (pure Boolean) for a truth assignment.
//! 3. **Theory-check** each theory's implied conjunction independently — integers
//!    and reals share no sort, so the combination is just propositional (no
//!    interface equalities). `sat` in both ⇒ build and replay a model; `unsat` in
//!    either ⇒ block the minimized conflict core and retry.
//!
//! Soundness: every model induces a skeleton-satisfying truth assignment whose
//! per-theory conjunctions are each satisfiable; the loop returns `sat` only
//! after replaying the original assertions, and `unsat` only when the skeleton
//! plus learned lemmas is propositionally unsatisfiable. A round budget bounds
//! the search (`unknown`, never wrong).

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{
    CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
};
use crate::lra::{check_with_lia_simplex, check_with_lra};
use crate::model::Model;
use crate::sat_bv_backend::SatBvBackend;

const ATOM_PREFIX: &str = "!arith_atom_";
const MAX_DPLL_ROUNDS: usize = 10_000;

/// The arithmetic theory an atom belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Theory {
    Int,
    Real,
}

/// Hard cap on Boolean symbols a refutation's propositional half may have to be
/// verified by exhaustive enumeration; above it the certificate is declined.
const MAX_CERTIFIABLE_BOOLS: usize = 22;

/// One literal of a learned theory lemma: the atom's proposition, the truth it
/// took in the conflict, the arithmetic literal (atom or its negation) used to
/// re-check the lemma, and the theory that decides it.
#[derive(Debug, Clone, Copy)]
pub struct ArithLemmaLiteral {
    /// The fresh Boolean proposition standing for the atom.
    pub prop: SymbolId,
    /// The truth value the proposition took in the (infeasible) assignment.
    pub truth: bool,
    /// The arithmetic literal: the atom term when `truth`, else its negation.
    pub literal: TermId,
    theory: Theory,
}

/// A checkable refutation of a Boolean-structured linear-arithmetic query: the
/// Boolean skeleton plus the learned theory lemmas (each an infeasible core).
/// [`Self::verify`] re-checks it independently of the search: every lemma core is
/// re-decided `unsat` by its theory's exact procedure, and the skeleton with all
/// lemma clauses is shown propositionally unsatisfiable by enumeration.
#[derive(Debug, Clone)]
pub struct ArithDpllRefutation {
    /// The Boolean skeleton (one term per assertion, arithmetic atoms as props).
    pub skeleton: Vec<TermId>,
    /// The learned theory lemmas; each is an infeasible core of arithmetic
    /// literals from a single theory.
    pub lemmas: Vec<Vec<ArithLemmaLiteral>>,
}

/// The outcome of [`certify_arith_dpll_unsat`].
#[derive(Debug, Clone)]
pub enum ArithDpllOutcome {
    /// Satisfiable, with a replayed model.
    Sat(Model),
    /// Unsatisfiable, with a self-checked refutation.
    Unsat(ArithDpllRefutation),
    /// Undecided / not certifiable, with a reason.
    Unknown(UnknownReason),
}

/// Decides a Boolean-structured linear-arithmetic query and, on `unsat`, returns
/// a self-checked [`ArithDpllRefutation`].
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for input outside Boolean-structured
/// linear arithmetic or with too many Boolean symbols to verify; or
/// [`SolverError::Backend`] if the refutation fails its own check (a soundness
/// alarm).
pub fn certify_arith_dpll_unsat(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<ArithDpllOutcome, SolverError> {
    let run = run_arith_dpll(arena, assertions, config)?;
    match run.result {
        CheckResult::Sat(model) => Ok(ArithDpllOutcome::Sat(model)),
        CheckResult::Unknown(reason) => Ok(ArithDpllOutcome::Unknown(reason)),
        CheckResult::Unsat => {
            let refutation = ArithDpllRefutation {
                skeleton: run.skeleton,
                lemmas: run.lemmas,
            };
            if refutation.verify(arena)? {
                Ok(ArithDpllOutcome::Unsat(refutation))
            } else {
                Err(SolverError::Backend(
                    "arith-dpll refutation failed its own self-check".to_string(),
                ))
            }
        }
    }
}

impl ArithDpllRefutation {
    /// The Boolean symbols (atom props and original Boolean variables) the
    /// refutation ranges over, in deterministic order.
    fn bool_symbols(&self, arena: &TermArena) -> Vec<SymbolId> {
        let mut set = std::collections::BTreeSet::new();
        let mut stack = self.skeleton.clone();
        let mut seen = HashSet::new();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match arena.node(t) {
                TermNode::Symbol(symbol) if arena.sort_of(t) == Sort::Bool => {
                    set.insert(*symbol);
                }
                TermNode::App { args, .. } => stack.extend(args.iter().copied()),
                _ => {}
            }
        }
        for lemma in &self.lemmas {
            for literal in lemma {
                set.insert(literal.prop);
            }
        }
        set.into_iter().collect()
    }

    /// Independently re-checks the refutation. Returns `Ok(true)` iff it holds.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Unsupported`] if there are too many Boolean symbols
    /// to enumerate, or [`SolverError`] from a theory re-check or evaluation.
    pub fn verify(&self, arena: &TermArena) -> Result<bool, SolverError> {
        // (1) Every lemma core is a genuine theory contradiction.
        for lemma in &self.lemmas {
            let lits: Vec<TermId> = lemma.iter().map(|l| l.literal).collect();
            if lits.is_empty() {
                return Ok(false);
            }
            let theory = lemma[0].theory;
            let unsat = match theory {
                Theory::Int => matches!(check_with_lia_simplex(arena, &lits)?, CheckResult::Unsat),
                Theory::Real => matches!(check_with_lra(arena, &lits)?, CheckResult::Unsat),
            };
            if !unsat {
                return Ok(false);
            }
        }

        // (2) skeleton AND every lemma clause is propositionally unsatisfiable.
        let bools = self.bool_symbols(arena);
        if bools.len() > MAX_CERTIFIABLE_BOOLS {
            return Err(SolverError::Unsupported(format!(
                "arith-dpll refutation has {} Boolean symbols, too many to verify by enumeration",
                bools.len()
            )));
        }
        let index_of: HashMap<SymbolId, usize> =
            bools.iter().enumerate().map(|(i, &s)| (s, i)).collect();
        let n = bools.len();
        for mask in 0u64..(1u64 << n) {
            let mut assignment = axeyum_ir::Assignment::new();
            for (i, &symbol) in bools.iter().enumerate() {
                assignment.set(symbol, Value::Bool((mask >> i) & 1 == 1));
            }
            let mut skeleton_holds = true;
            for &term in &self.skeleton {
                match eval(arena, term, &assignment) {
                    Ok(Value::Bool(true)) => {}
                    Ok(_) => {
                        skeleton_holds = false;
                        break;
                    }
                    Err(error) => {
                        return Err(SolverError::Backend(format!(
                            "arith-dpll verify: skeleton evaluation error: {error}"
                        )));
                    }
                }
            }
            if !skeleton_holds {
                continue;
            }
            // A lemma clause (the core's negation) is false exactly when the core
            // is fully satisfied; the refutation needs at least one clause false.
            let all_clauses_hold = self.lemmas.iter().all(|lemma| {
                let core_fully_satisfied = lemma
                    .iter()
                    .all(|l| (mask >> index_of[&l.prop]) & 1 == u64::from(l.truth));
                !core_fully_satisfied
            });
            if all_clauses_hold {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// Decides a Boolean-structured `QF_LIA` query (integer atoms only) by lazy-SMT.
///
/// A thin wrapper over [`check_with_arith_dpll`]; kept as a named entry point for
/// the integer dispatcher.
///
/// # Errors
///
/// See [`check_with_arith_dpll`].
pub fn check_with_lia_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    check_with_arith_dpll(arena, assertions, config)
}

/// Decides a Boolean-structured linear-arithmetic query — integer, real, or
/// combined `QF_LIRA` — by lazy-SMT over the exact-rational simplices.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion is not Boolean structure
/// over linear-arithmetic atoms (e.g. it mentions bit-vectors, arrays, or
/// functions), so the caller can fall back; or [`SolverError::Backend`] on a
/// replay alarm.
pub fn check_with_arith_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    Ok(run_arith_dpll(arena, assertions, config)?.result)
}

/// The lazy-SMT loop plus the trace needed to certify an `unsat` (the Boolean
/// skeleton and the learned theory lemmas).
struct ArithRun {
    result: CheckResult,
    skeleton: Vec<TermId>,
    lemmas: Vec<Vec<ArithLemmaLiteral>>,
}

fn run_arith_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<ArithRun, SolverError> {
    let mut ctx = ArithAbstractor::default();
    let mut skeleton = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        skeleton.push(ctx.abstract_term(arena, assertion)?);
    }

    let mut backend = SatBvBackend::new();
    let mut blocking: Vec<TermId> = Vec::new();
    let mut lemmas: Vec<Vec<ArithLemmaLiteral>> = Vec::new();

    for _ in 0..MAX_DPLL_ROUNDS {
        let mut sat_assertions = skeleton.clone();
        sat_assertions.extend(blocking.iter().copied());
        let propositional = match backend.check(arena, &sat_assertions, config)? {
            CheckResult::Sat(model) => model,
            CheckResult::Unsat => {
                return Ok(ArithRun {
                    result: CheckResult::Unsat,
                    skeleton,
                    lemmas,
                });
            }
            CheckResult::Unknown(reason) => {
                return Ok(ArithRun {
                    result: CheckResult::Unknown(reason),
                    skeleton,
                    lemmas,
                });
            }
        };

        // The arithmetic literal implied by this assignment for each atom, in
        // `ctx.atoms` order.
        let mut truths = Vec::with_capacity(ctx.atoms.len());
        let mut lits = Vec::with_capacity(ctx.atoms.len());
        for atom in &ctx.atoms {
            let truth = propositional
                .get(atom.prop)
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            truths.push(truth);
            lits.push(if truth {
                atom.term
            } else {
                arena.not(atom.term)?
            });
        }

        // Theory-check each theory's conjunction independently.
        if let Some(conflict) =
            theory_conflict(arena, &ctx, &lits, Theory::Int, check_with_lia_simplex)?
        {
            lemmas.push(record_lemma(&ctx, &truths, &lits, &conflict));
            blocking.push(block_clause(arena, &ctx.atoms, &truths, &conflict)?);
            continue;
        }
        if let Some(conflict) = theory_conflict(arena, &ctx, &lits, Theory::Real, check_with_lra)? {
            lemmas.push(record_lemma(&ctx, &truths, &lits, &conflict));
            blocking.push(block_clause(arena, &ctx.atoms, &truths, &conflict)?);
            continue;
        }

        // Both theories consistent: build and replay the combined model.
        let result = finish_sat(arena, assertions, &ctx, &propositional, &lits)?;
        return Ok(ArithRun {
            result,
            skeleton,
            lemmas,
        });
    }

    Ok(ArithRun {
        result: CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!("lazy linear arithmetic exceeded {MAX_DPLL_ROUNDS} refinement rounds"),
        }),
        skeleton,
        lemmas,
    })
}

/// Records a theory conflict core as a structured lemma for certification.
fn record_lemma(
    ctx: &ArithAbstractor,
    truths: &[bool],
    lits: &[TermId],
    core: &[usize],
) -> Vec<ArithLemmaLiteral> {
    core.iter()
        .map(|&i| ArithLemmaLiteral {
            prop: ctx.atoms[i].prop,
            truth: truths[i],
            literal: lits[i],
            theory: ctx.atoms[i].theory,
        })
        .collect()
}

/// Checks one theory's conjunction; on `unsat`, returns the minimized conflict
/// core as global atom indices. `oracle` is the conjunctive decision procedure
/// for the theory.
fn theory_conflict(
    arena: &TermArena,
    ctx: &ArithAbstractor,
    lits: &[TermId],
    theory: Theory,
    oracle: fn(&TermArena, &[TermId]) -> Result<CheckResult, SolverError>,
) -> Result<Option<Vec<usize>>, SolverError> {
    let indices: Vec<usize> = (0..ctx.atoms.len())
        .filter(|&i| ctx.atoms[i].theory == theory)
        .collect();
    if indices.is_empty() {
        return Ok(None);
    }
    let conj: Vec<TermId> = indices.iter().map(|&i| lits[i]).collect();
    if !matches!(oracle(arena, &conj)?, CheckResult::Unsat) {
        return Ok(None);
    }
    Ok(Some(minimize_core(arena, &indices, lits, oracle)?))
}

/// Deletion-based minimization: returns a minimal still-unsatisfiable subset of
/// `indices` (global atom indices). Each surviving member is necessary, so the
/// negated core is a strong, sound lemma.
fn minimize_core(
    arena: &TermArena,
    indices: &[usize],
    lits: &[TermId],
    oracle: fn(&TermArena, &[TermId]) -> Result<CheckResult, SolverError>,
) -> Result<Vec<usize>, SolverError> {
    let mut core: Vec<usize> = indices.to_vec();
    for &candidate in indices {
        if !core.contains(&candidate) {
            continue;
        }
        let trial: Vec<TermId> = core
            .iter()
            .filter(|&&i| i != candidate)
            .map(|&i| lits[i])
            .collect();
        if !trial.is_empty() && matches!(oracle(arena, &trial)?, CheckResult::Unsat) {
            core.retain(|&i| i != candidate);
        }
    }
    Ok(core)
}

/// Builds the combined model (integers from the integer simplex, reals from the
/// real engine, Booleans from the skeleton) and replays the original assertions.
fn finish_sat(
    arena: &mut TermArena,
    assertions: &[TermId],
    ctx: &ArithAbstractor,
    propositional: &Model,
    lits: &[TermId],
) -> Result<CheckResult, SolverError> {
    // Re-decide each theory's conjunction to recover its model (the loop only
    // learned that they are *consistent*).
    let int_lits: Vec<TermId> = atom_lits(ctx, lits, Theory::Int);
    let real_lits: Vec<TermId> = atom_lits(ctx, lits, Theory::Real);
    let int_model = theory_model(arena, &int_lits, check_with_lia_simplex)?;
    let real_model = theory_model(arena, &real_lits, check_with_lra)?;

    let mut model = Model::new();
    let mut assignment = axeyum_ir::Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        if ctx.is_atom_prop(symbol) || name.starts_with(ATOM_PREFIX) {
            continue;
        }
        let value = match sort {
            Sort::Int => int_model.as_ref().and_then(|m| m.get(symbol)),
            Sort::Real => real_model.as_ref().and_then(|m| m.get(symbol)),
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
                    "arith dpll sat model replay failed: assertion #{} not satisfied",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "arith dpll sat model replay error on assertion #{}: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(CheckResult::Sat(model))
}

/// The literals of one theory's atoms.
fn atom_lits(ctx: &ArithAbstractor, lits: &[TermId], theory: Theory) -> Vec<TermId> {
    (0..ctx.atoms.len())
        .filter(|&i| ctx.atoms[i].theory == theory)
        .map(|i| lits[i])
        .collect()
}

/// Re-decides a consistent theory conjunction to recover its model.
fn theory_model(
    arena: &TermArena,
    lits: &[TermId],
    oracle: fn(&TermArena, &[TermId]) -> Result<CheckResult, SolverError>,
) -> Result<Option<Model>, SolverError> {
    if lits.is_empty() {
        return Ok(None);
    }
    match oracle(arena, lits)? {
        CheckResult::Sat(model) => Ok(Some(model)),
        // The loop already established consistency, so this is unreachable; treat
        // as no extra bindings rather than failing.
        _ => Ok(None),
    }
}

/// A clause forcing at least one atom in `core` to flip from `truths`. `core`
/// indexes `atoms`/`truths`.
fn block_clause(
    arena: &mut TermArena,
    atoms: &[ArithAtom],
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
    clause.ok_or_else(|| SolverError::Backend("arith dpll: empty conflict clause".to_string()))
}

/// One abstracted arithmetic order atom: its fresh proposition, the atom term,
/// and which theory decides it.
struct ArithAtom {
    prop: SymbolId,
    term: TermId,
    theory: Theory,
}

/// Abstracts Boolean structure over linear-arithmetic atoms into a propositional
/// skeleton.
#[derive(Default)]
struct ArithAbstractor {
    atom_of: HashMap<TermId, SymbolId>,
    props: HashSet<SymbolId>,
    atoms: Vec<ArithAtom>,
    fresh_counter: usize,
}

impl ArithAbstractor {
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
                    let prop = self.atom(arena, term, Theory::Int);
                    Ok(arena.var(prop))
                }
                Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe => {
                    let prop = self.atom(arena, term, Theory::Real);
                    Ok(arena.var(prop))
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Int => {
                    let le = arena.int_le(args[0], args[1])?;
                    let ge = arena.int_ge(args[0], args[1])?;
                    let le_prop = self.abstract_term(arena, le)?;
                    let ge_prop = self.abstract_term(arena, ge)?;
                    Ok(arena.and(le_prop, ge_prop)?)
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Real => {
                    let le = arena.real_le(args[0], args[1])?;
                    let ge = arena.real_ge(args[0], args[1])?;
                    let le_prop = self.abstract_term(arena, le)?;
                    let ge_prop = self.abstract_term(arena, ge)?;
                    Ok(arena.and(le_prop, ge_prop)?)
                }
                _ => Err(SolverError::Unsupported(
                    "lazy arithmetic: assertion is not Boolean structure over linear-arithmetic \
                     atoms"
                        .to_owned(),
                )),
            },
            _ => Err(SolverError::Unsupported(
                "lazy arithmetic: non-Boolean, non-arithmetic-atom term in a Boolean position"
                    .to_owned(),
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

    fn atom(&mut self, arena: &mut TermArena, term: TermId, theory: Theory) -> SymbolId {
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
        self.atoms.push(ArithAtom { prop, term, theory });
        prop
    }
}
