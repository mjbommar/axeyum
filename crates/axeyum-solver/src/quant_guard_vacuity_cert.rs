//! Independently checked outer-BV witnesses for false guarded quantifier matrices.

use std::collections::BTreeSet;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};

/// A concrete outer witness that makes an exact guarded quantified assertion true.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedGuardSatCertificate {
    /// The untouched original assertion covered by this certificate.
    pub assertion: TermId,
    /// The assertion's outer existential binder.
    pub existential: SymbolId,
    /// A concrete bit-vector value for `existential`.
    pub witness: Value,
}

/// Checks an exact false-equality guard below direct Bool/BV quantifier alternation.
///
/// The admitted source shape is `exists x. Q*. ((x = k) => consequent)`, with
/// either equality operand order and at least one nested quantifier in `Q*`.
/// `consequent` remains opaque because a witness unequal to `k` makes the
/// implication true for every nested assignment.
#[must_use]
pub fn check_quantified_guard_sat(
    arena: &TermArena,
    assertion: TermId,
    cert: &QuantifiedGuardSatCertificate,
) -> bool {
    if cert.assertion != assertion {
        return false;
    }
    let TermNode::App {
        op: Op::Exists(existential),
        args,
    } = arena.node(assertion)
    else {
        return false;
    };
    let [body] = &**args else {
        return false;
    };
    let outer_sort = arena.symbol(*existential).1;
    if *existential != cert.existential
        || !matches!(outer_sort, Sort::BitVec(_))
        || cert.witness.sort() != outer_sort
    {
        return false;
    }

    let mut binders = BTreeSet::from([*existential]);
    let mut cursor = *body;
    let mut nested = 0usize;
    while let TermNode::App {
        op: Op::Forall(binder) | Op::Exists(binder),
        args,
    } = arena.node(cursor)
    {
        let [next] = &**args else {
            return false;
        };
        if !binders.insert(*binder)
            || !matches!(arena.symbol(*binder).1, Sort::Bool | Sort::BitVec(_))
        {
            return false;
        }
        nested += 1;
        cursor = *next;
    }
    if nested == 0 {
        return false;
    }

    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(cursor)
    else {
        return false;
    };
    let [antecedent, _consequent] = &**args else {
        return false;
    };
    let Some(guard_constant) = equality_guard_constant(arena, *antecedent, *existential) else {
        return false;
    };
    guard_constant.sort() == outer_sort && cert.witness != guard_constant
}

fn equality_guard_constant(
    arena: &TermArena,
    term: TermId,
    existential: SymbolId,
) -> Option<Value> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    if matches!(arena.node(*left), TermNode::Symbol(symbol) if *symbol == existential) {
        bit_vector_constant(arena, *right)
    } else if matches!(arena.node(*right), TermNode::Symbol(symbol) if *symbol == existential) {
        bit_vector_constant(arena, *left)
    } else {
        None
    }
}

fn bit_vector_constant(arena: &TermArena, term: TermId) -> Option<Value> {
    match arena.node(term) {
        TermNode::BvConst { width, value } => Some(Value::Bv {
            width: *width,
            value: *value,
        }),
        TermNode::WideBvConst(value) => Some(Value::WideBv(value.clone())),
        _ => None,
    }
}
