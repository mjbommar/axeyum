//! Term-level certification by exhaustive evaluation (the trust dual of model
//! replay).
//!
//! Model replay certifies a `sat` result using only the ground evaluator. This
//! module does the same for `unsat` on small `QF_BV`/Boolean instances:
//! [`certify_qf_bv_by_enumeration`] enumerates **every** assignment over the
//! finite symbol domain and evaluates the original assertions. If none
//! satisfies them, that is an oracle-free, machine-checkable certificate of
//! `unsat` *at the term level* — independent of the bit-blaster, CNF encoder,
//! and SAT solver (it uses only `axeyum-ir`'s evaluator). If some assignment
//! satisfies them, it is returned as a model. The cost is exponential in the
//! total symbol width, so it applies to small instances (mirroring the
//! exhaustive scenario self-checks), complementing the scalable DRAT proof that
//! certifies only the clausal layer.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, TermNode, Value, eval};

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
    for &assertion in assertions {
        if arena.sort_of(assertion) != Sort::Bool {
            return Err(SolverError::NonBooleanAssertion(assertion));
        }
    }
    let symbols = collect_enumerable_symbols(arena, assertions)?;
    let total_bits: u32 = symbols.iter().map(|&(_, sort)| sort_bits(sort)).sum();
    if total_bits > max_total_bits {
        return Ok(CertifyOutcome::DomainTooLarge { total_bits });
    }

    let cases = 1u64 << total_bits;
    for code in 0..cases {
        let assignment = decode_assignment(&symbols, u128::from(code));
        if satisfies_all(arena, assertions, &assignment)? {
            return Ok(CertifyOutcome::Satisfiable(model_from(
                &symbols,
                &assignment,
            )));
        }
    }
    Ok(CertifyOutcome::CertifiedUnsat { cases })
}

/// Collects the `(symbol, sort)` pairs to enumerate, rejecting anything not
/// finitely enumerable from the symbol domain alone.
fn collect_enumerable_symbols(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Vec<(axeyum_ir::SymbolId, Sort)>, SolverError> {
    let mut seen = std::collections::BTreeSet::new();
    let mut symbols = Vec::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
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
                if matches!(
                    op,
                    Op::Apply(_) | Op::Select | Op::Store | Op::Forall(_) | Op::Exists(_)
                ) {
                    return Err(SolverError::Unsupported(
                        "enumeration certificate: query uses functions, arrays, or quantifiers"
                            .to_owned(),
                    ));
                }
                stack.extend(args.iter().copied());
            }
            TermNode::IntConst(_) | TermNode::RealConst(_) => {
                return Err(SolverError::Unsupported(
                    "enumeration certificate: query uses integer/real arithmetic".to_owned(),
                ));
            }
            TermNode::BoolConst(_) | TermNode::BvConst { .. } => {}
        }
    }
    // Deduplicate (a symbol may be reached via several terms) and order
    // deterministically by symbol id.
    symbols.sort_unstable_by_key(|&(symbol, _)| symbol.index());
    symbols.dedup_by_key(|&mut (symbol, _)| symbol.index());
    Ok(symbols)
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
