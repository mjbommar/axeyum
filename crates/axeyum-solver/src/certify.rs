//! Term-level certification by exhaustive evaluation (the trust dual of model
//! replay).
//!
//! Model replay certifies a `sat` result using only the ground evaluator. This
//! module does the same for `unsat` on small `QF_BV`/Boolean instances:
//! [`certify_qf_bv_by_enumeration`] enumerates **every** assignment over the
//! finite symbol domain and evaluates the original assertions. The companion
//! [`certify_finite_bv_by_enumeration`] permits finite Bool/BV quantifiers and
//! counts their bound domains in the same budget while relying on the evaluator
//! to execute their semantics. If no free assignment satisfies the assertions,
//! that is an oracle-free, machine-checkable certificate of `unsat` *at the term
//! level* — independent of the bit-blaster, CNF encoder, and SAT solver (it uses
//! only `axeyum-ir`'s evaluator). If some assignment satisfies them, it is
//! returned as a model. The cost is exponential in the finite domain width, so
//! it applies to small instances (mirroring the exhaustive scenario self-checks),
//! complementing the scalable DRAT proof that certifies only the clausal layer.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::SolverError;
use crate::model::Model;

/// The result of attempting term-level certification by enumeration.
#[derive(Debug, Clone)]
pub enum CertifyOutcome {
    /// No assignment over the finite domain satisfies the assertions — a
    /// term-level `unsat` certificate (the count of cases checked).
    CertifiedUnsat {
        /// Number of assignments exhaustively evaluated.
        cases: u64,
    },
    /// An assignment satisfying every assertion was found.
    Satisfiable(Model),
    /// The combined symbol domain exceeds the bit budget; not attempted.
    DomainTooLarge {
        /// Total symbol width that exceeded `max_total_bits`.
        total_bits: u32,
    },
}

/// Certifies a `QF_BV`/Boolean conjunction by exhaustively evaluating the
/// original assertions over all symbol assignments, up to `max_total_bits` of
/// combined symbol width.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion uses a sort or operator
/// outside finitely-enumerable `QF_BV`/Boolean (integers, reals, arrays,
/// uninterpreted functions, or quantifiers), or
/// [`SolverError::NonBooleanAssertion`] for a non-Boolean assertion.
pub fn certify_qf_bv_by_enumeration(
    arena: &TermArena,
    assertions: &[TermId],
    max_total_bits: u32,
) -> Result<CertifyOutcome, SolverError> {
    certify_bv_by_enumeration(arena, assertions, max_total_bits, false)
}

/// Certifies a finite Bool/BV conjunction by exhaustively evaluating the
/// original assertions over all free-symbol assignments, while allowing finite
/// Bool/BV quantifiers in the terms themselves.
///
/// Bound quantifier domains are counted toward `max_total_bits` and are evaluated
/// by `axeyum-ir`'s executable quantifier semantics. Uninterpreted functions,
/// arrays, integers, reals, and non-Bool/BV quantifier domains are rejected.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion uses a sort or operator
/// outside finitely-enumerable Bool/BV, or
/// [`SolverError::NonBooleanAssertion`] for a non-Boolean assertion.
pub fn certify_finite_bv_by_enumeration(
    arena: &TermArena,
    assertions: &[TermId],
    max_total_bits: u32,
) -> Result<CertifyOutcome, SolverError> {
    certify_bv_by_enumeration(arena, assertions, max_total_bits, true)
}

fn certify_bv_by_enumeration(
    arena: &TermArena,
    assertions: &[TermId],
    max_total_bits: u32,
    allow_quantifiers: bool,
) -> Result<CertifyOutcome, SolverError> {
    for &assertion in assertions {
        if arena.sort_of(assertion) != Sort::Bool {
            return Err(SolverError::NonBooleanAssertion(assertion));
        }
    }
    let (symbols, quantified_bits) =
        collect_enumerable_symbols(arena, assertions, allow_quantifiers)?;
    let free_bits: u32 = symbols.iter().map(|&(_, sort)| sort_bits(sort)).sum();
    let total_bits = free_bits.checked_add(quantified_bits).ok_or_else(|| {
        SolverError::Unsupported("enumeration certificate: domain width overflow".to_owned())
    })?;
    if total_bits > max_total_bits {
        return Ok(CertifyOutcome::DomainTooLarge { total_bits });
    }
    if total_bits >= u64::BITS {
        return Ok(CertifyOutcome::DomainTooLarge { total_bits });
    }

    let free_cases = case_count(free_bits);
    for code in 0..free_cases {
        let assignment = decode_assignment(&symbols, u128::from(code));
        if satisfies_all(arena, assertions, &assignment)? {
            return Ok(CertifyOutcome::Satisfiable(model_from(
                &symbols,
                &assignment,
            )));
        }
    }
    let cases = case_count(total_bits);
    Ok(CertifyOutcome::CertifiedUnsat { cases })
}

/// Per-call memo tables for [`collect_enumerable_symbols_rec`].
///
/// # Why a memo is needed (and why it is sound)
///
/// The arena is a **shared DAG**, not a tree: `axeyum-ir` interns terms, so one
/// node is reached along many paths. A plain structural recursion therefore
/// walks the *tree unfolding*, whose size is exponential in the sharing depth.
/// Measured on `QF_BVFP/.../solver__fp__Float-no-simp3-main.smt2` (a ~3,000-node
/// arena): 1.28e10 calls in 90 s and still climbing, with flat RSS and a flat
/// 136 kB stack — the signature of re-walking shared subtrees, not of deep
/// recursion or allocation. It is the third instance of this same bug (after
/// `contains_quantifier` and `lower_derived_bv`, both fixed in `e14a13b5d`).
///
/// The two things this walk computes have *different* purity, so they get
/// different tables:
///
/// - **Free symbols** are scope-dependent: `bound` records the quantifier
///   variables in scope, and a `Symbol` node is skipped exactly when it is
///   bound. The same term under two different scopes can therefore contribute
///   different symbols, so `visited` is keyed by `(term, scope)` — the whole
///   bound stack, not just the term. That makes a memo hit mean "this exact
///   `(term, scope)` pair already contributed everything it can", which is
///   sound because the walk is deterministic and its only symbol effect is
///   pushing onto `symbols`, which the caller sorts and dedups anyway.
/// - **Quantified bits** are scope-*independent*: they depend only on which
///   `Forall`/`Exists` nodes the subterm contains and on their variables'
///   sorts. So `quantified_bits` is keyed by term alone.
///
/// Crucially, `quantified_bits` must stay a sum over the **tree unfolding**,
/// not over distinct DAG nodes: it is the budget proxy for how much work the
/// evaluator will do, and the evaluator re-enumerates a shared quantifier once
/// per occurrence. Counting distinct nodes would undercount an exponentially
/// shared nest and let a query that cannot be enumerated past the budget check.
/// So the recursion *returns* its subtree's tree-sum and each caller adds it
/// once per argument occurrence; the memo only avoids recomputing that number,
/// it never collapses two occurrences into one.
///
/// Both tables are created per call and dropped with it, over a `&TermArena`
/// that cannot change while they live — so a cached entry can never go stale
/// against later arena growth.
#[derive(Default)]
struct EnumerableSymbolMemo {
    /// `(term, bound-scope)` pairs whose free symbols are already in `symbols`.
    visited: BTreeSet<(TermId, Vec<SymbolId>)>,
    /// `term` → quantified bits in its **tree unfolding**.
    quantified_bits: BTreeMap<TermId, u32>,
}

/// Collects the `(symbol, sort)` pairs to enumerate, rejecting anything not
/// finitely enumerable from the symbol domain alone.
fn collect_enumerable_symbols(
    arena: &TermArena,
    assertions: &[TermId],
    allow_quantifiers: bool,
) -> Result<(Vec<(SymbolId, Sort)>, u32), SolverError> {
    let mut symbols = Vec::new();
    let mut quantified_bits = 0u32;
    let mut bound = Vec::new();
    let mut memo = EnumerableSymbolMemo::default();
    for &assertion in assertions {
        // Per assertion, not per distinct node: two assertions sharing a
        // quantified subterm each pay for it, exactly as the unmemoized walk did.
        let bits = collect_enumerable_symbols_rec(
            arena,
            assertion,
            &mut bound,
            &mut symbols,
            allow_quantifiers,
            &mut memo,
        )?;
        quantified_bits = add_bits(quantified_bits, bits)?;
    }
    // Deduplicate (a symbol may be reached via several terms) and order
    // deterministically by symbol id.
    symbols.sort_unstable_by_key(|&(symbol, _)| symbol.index());
    symbols.dedup_by_key(|&mut (symbol, _)| symbol.index());
    Ok((symbols, quantified_bits))
}

/// Adds two quantified-domain widths, reporting overflow as the same
/// `Unsupported` decline the unmemoized walk produced.
fn add_bits(left: u32, right: u32) -> Result<u32, SolverError> {
    left.checked_add(right).ok_or_else(|| {
        SolverError::Unsupported(
            "enumeration certificate: quantified domain width overflow".to_owned(),
        )
    })
}

/// Walks `term`, pushing its free symbols onto `symbols`, and returns the
/// quantified-domain width of its **tree unfolding** (see
/// [`EnumerableSymbolMemo`] for why that is a tree sum and the memo is sound).
fn collect_enumerable_symbols_rec(
    arena: &TermArena,
    term: TermId,
    bound: &mut Vec<SymbolId>,
    symbols: &mut Vec<(SymbolId, Sort)>,
    allow_quantifiers: bool,
    memo: &mut EnumerableSymbolMemo,
) -> Result<u32, SolverError> {
    // A hit is recorded only after a subtree completed with `Ok`, so skipping it
    // can never mask an error the unmemoized walk would have reported.
    if memo.visited.contains(&(term, bound.clone())) {
        return Ok(memo.quantified_bits.get(&term).copied().unwrap_or(0));
    }
    let mut bits = 0u32;
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            if bound.contains(symbol) {
                memo.visited.insert((term, bound.clone()));
                return Ok(0);
            }
            let sort = arena.sort_of(term);
            if !matches!(sort, Sort::Bool | Sort::BitVec(_)) {
                return Err(SolverError::Unsupported(format!(
                    "enumeration certificate: symbol of sort {sort} is not finitely enumerable"
                )));
            }
            symbols.push((*symbol, sort));
        }
        TermNode::App { op, args } => {
            use axeyum_ir::Op;
            match op {
                Op::Apply(_) | Op::Select | Op::Store => {
                    return Err(SolverError::Unsupported(
                        "enumeration certificate: query uses functions or arrays".to_owned(),
                    ));
                }
                Op::Forall(var) | Op::Exists(var) => {
                    if !allow_quantifiers {
                        return Err(SolverError::Unsupported(
                            "enumeration certificate: query uses quantifiers".to_owned(),
                        ));
                    }
                    let sort = arena.symbol(*var).1;
                    if !matches!(sort, Sort::Bool | Sort::BitVec(_)) {
                        return Err(SolverError::Unsupported(format!(
                            "enumeration certificate: quantified symbol of sort {sort} is not \
                             finitely enumerable"
                        )));
                    }
                    bits = add_bits(bits, sort_bits(sort))?;
                    bound.push(*var);
                    for &arg in &**args {
                        let arg_bits = collect_enumerable_symbols_rec(
                            arena,
                            arg,
                            bound,
                            symbols,
                            allow_quantifiers,
                            memo,
                        );
                        match arg_bits {
                            Ok(arg_bits) => bits = add_bits(bits, arg_bits)?,
                            Err(error) => {
                                bound.pop();
                                return Err(error);
                            }
                        }
                    }
                    bound.pop();
                }
                _ => {
                    for &arg in &**args {
                        let arg_bits = collect_enumerable_symbols_rec(
                            arena,
                            arg,
                            bound,
                            symbols,
                            allow_quantifiers,
                            memo,
                        )?;
                        bits = add_bits(bits, arg_bits)?;
                    }
                }
            }
        }
        TermNode::IntConst(_) | TermNode::RealConst(_) => {
            return Err(SolverError::Unsupported(
                "enumeration certificate: query uses integer/real arithmetic".to_owned(),
            ));
        }
        TermNode::BoolConst(_) | TermNode::BvConst { .. } | TermNode::WideBvConst(_) => {}
    }
    memo.visited.insert((term, bound.clone()));
    memo.quantified_bits.insert(term, bits);
    Ok(bits)
}

fn satisfies_all(
    arena: &TermArena,
    assertions: &[TermId],
    assignment: &Assignment,
) -> Result<bool, SolverError> {
    for &assertion in assertions {
        match eval(arena, assertion, assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return Ok(false),
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "enumeration certificate: assertion #{} is non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "enumeration certificate: assertion #{} failed to evaluate: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(true)
}

fn decode_assignment(symbols: &[(axeyum_ir::SymbolId, Sort)], code: u128) -> Assignment {
    let mut assignment = Assignment::new();
    let mut offset = 0u32;
    for &(symbol, sort) in symbols {
        let bits = sort_bits(sort);
        let field = (code >> offset) & mask(bits);
        assignment.set(symbol, decode_value(sort, field));
        offset += bits;
    }
    assignment
}

fn model_from(symbols: &[(axeyum_ir::SymbolId, Sort)], assignment: &Assignment) -> Model {
    let mut model = Model::new();
    for &(symbol, _) in symbols {
        if let Some(value) = assignment.get(symbol) {
            model.set(symbol, value);
        }
    }
    model
}

fn decode_value(sort: Sort, field: u128) -> Value {
    match sort {
        Sort::Bool => Value::Bool(field & 1 == 1),
        Sort::BitVec(width) => Value::Bv {
            width,
            value: field,
        },
        // `collect_enumerable_symbols` rejects every other sort.
        other => unreachable!("non-enumerable sort {other} reached decoding"),
    }
}

fn sort_bits(sort: Sort) -> u32 {
    match sort {
        Sort::Bool => 1,
        Sort::BitVec(width) => width,
        other => unreachable!("non-enumerable sort {other} reached bit counting"),
    }
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn case_count(bits: u32) -> u64 {
    1u64 << bits
}
