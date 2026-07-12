//! Source-bound quantified-BV model certificates (ADR-0130).
//!
//! Candidate search is deliberately outside this module. The checker below
//! proves an untouched assertion under a complete free-BV assignment by either
//! an affine least-significant-bit invariant or a concrete counterexample to a
//! directly negated universal.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

/// Maximum total quantifier binders admitted by one certificate.
pub const QUANT_BV_MODEL_BINDER_CAP: usize = 128;
/// Maximum complete source DAG nodes admitted by one certificate.
pub const QUANT_BV_MODEL_NODE_CAP: usize = 4_096;
/// Maximum source depth admitted by the recursive proof evaluator.
pub const QUANT_BV_MODEL_DEPTH_CAP: usize = 256;

/// The independently checked proof attached to one quantified BV assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifiedBvModelSatProof {
    /// A direct universal body is true because a BV equality below its Boolean
    /// structure has affine LSB forms that differ for every binder assignment.
    AffineLsbUniversal,
    /// A direct negated universal is true at this complete binder assignment.
    NegatedUniversalWitness {
        /// Universal binders, outermost first.
        binders: Vec<SymbolId>,
        /// One exact Bool/BV value for every binder.
        values: Vec<Value>,
    },
}

/// A complete free-BV interpretation and source-level proof for one assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedBvModelSatCertificate {
    /// The untouched original assertion covered by this certificate.
    pub assertion: TermId,
    /// Exact, strictly ordered values for every free symbol in the assertion.
    pub free_values: Vec<(SymbolId, Value)>,
    /// The source-level proof checked independently from candidate search.
    pub proof: QuantifiedBvModelSatProof,
}

/// Checks a quantified-BV model certificate against untouched original IR.
#[must_use]
pub fn check_quantified_bv_model_sat(
    arena: &TermArena,
    assertion: TermId,
    cert: &QuantifiedBvModelSatCertificate,
) -> bool {
    if cert.assertion != assertion {
        return false;
    }
    let Some(shape) = source_shape(arena, assertion) else {
        return false;
    };
    let Some(free_values) = checked_free_values(arena, &shape.free, &cert.free_values) else {
        return false;
    };
    match &cert.proof {
        QuantifiedBvModelSatProof::AffineLsbUniversal => {
            check_affine_lsb_universal(arena, assertion, &shape, &free_values)
        }
        QuantifiedBvModelSatProof::NegatedUniversalWitness { binders, values } => {
            check_negated_universal_witness(arena, assertion, &shape, &free_values, binders, values)
        }
    }
}

#[derive(Debug)]
struct SourceShape {
    binders: BTreeSet<SymbolId>,
    free: Vec<SymbolId>,
}

fn source_shape(arena: &TermArena, root: TermId) -> Option<SourceShape> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![(root, 1usize)];
    let mut binders = BTreeSet::new();
    let mut symbols = BTreeSet::new();
    while let Some((term, depth)) = stack.pop() {
        if depth > QUANT_BV_MODEL_DEPTH_CAP
            || !matches!(arena.sort_of(term), Sort::Bool | Sort::BitVec(_))
        {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > QUANT_BV_MODEL_NODE_CAP {
            return None;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                if !matches!(arena.symbol(*symbol).1, Sort::Bool | Sort::BitVec(_)) {
                    return None;
                }
                symbols.insert(*symbol);
            }
            TermNode::App { op, args } => {
                if matches!(op, Op::Apply(_)) {
                    return None;
                }
                if let Op::Forall(binder) | Op::Exists(binder) = op
                    && (!binders.insert(*binder)
                        || binders.len() > QUANT_BV_MODEL_BINDER_CAP
                        || !matches!(arena.symbol(*binder).1, Sort::Bool | Sort::BitVec(_))
                        || args.len() != 1)
                {
                    return None;
                }
                stack.extend(args.iter().map(|&argument| (argument, depth + 1)));
            }
            TermNode::BoolConst(_) | TermNode::BvConst { .. } | TermNode::WideBvConst(_) => {}
            TermNode::IntConst(_) | TermNode::RealConst(_) => return None,
        }
    }
    let free = symbols.difference(&binders).copied().collect::<Vec<_>>();
    if free
        .iter()
        .any(|symbol| !matches!(arena.symbol(*symbol).1, Sort::BitVec(_)))
    {
        return None;
    }
    Some(SourceShape { binders, free })
}

fn checked_free_values(
    arena: &TermArena,
    expected: &[SymbolId],
    values: &[(SymbolId, Value)],
) -> Option<BTreeMap<SymbolId, Value>> {
    if expected.len() != values.len()
        || expected
            .iter()
            .zip(values)
            .any(|(&expected, (actual, value))| {
                expected != *actual || value.sort() != arena.symbol(expected).1
            })
    {
        return None;
    }
    Some(values.iter().cloned().collect())
}

fn check_affine_lsb_universal(
    arena: &TermArena,
    assertion: TermId,
    shape: &SourceShape,
    free: &BTreeMap<SymbolId, Value>,
) -> bool {
    let Some((binders, body)) = peel_prefix(arena, assertion, true) else {
        return false;
    };
    if binders.is_empty()
        || binders.iter().copied().collect::<BTreeSet<_>>() != shape.binders
        || contains_quantifier(arena, body)
    {
        return false;
    }
    prove_bool(arena, body, &shape.binders, free) == Truth::True
}

fn check_negated_universal_witness(
    arena: &TermArena,
    assertion: TermId,
    shape: &SourceShape,
    free: &BTreeMap<SymbolId, Value>,
    claimed_binders: &[SymbolId],
    values: &[Value],
) -> bool {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(assertion)
    else {
        return false;
    };
    let [inner] = &**args else {
        return false;
    };
    let Some((binders, body)) = peel_prefix(arena, *inner, true) else {
        return false;
    };
    if binders.is_empty()
        || binders != claimed_binders
        || binders.iter().copied().collect::<BTreeSet<_>>() != shape.binders
        || binders.len() != values.len()
        || contains_quantifier(arena, body)
        || binders
            .iter()
            .zip(values)
            .any(|(&binder, value)| value.sort() != arena.symbol(binder).1)
    {
        return false;
    }
    let mut assignment = Assignment::new();
    for (&symbol, value) in free {
        assignment.set(symbol, value.clone());
    }
    for (&binder, value) in binders.iter().zip(values) {
        assignment.set(binder, value.clone());
    }
    matches!(eval(arena, body, &assignment), Ok(Value::Bool(false)))
}

fn peel_prefix(arena: &TermArena, root: TermId, forall: bool) -> Option<(Vec<SymbolId>, TermId)> {
    let mut binders = Vec::new();
    let mut cursor = root;
    while let TermNode::App { op, args } = arena.node(cursor) {
        let binder = match op {
            Op::Forall(binder) if forall => *binder,
            Op::Exists(binder) if !forall => *binder,
            _ => break,
        };
        let [body] = &**args else {
            return None;
        };
        binders.push(binder);
        cursor = *body;
    }
    Some((binders, cursor))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Truth {
    False,
    Unknown,
    True,
}

fn prove_bool(
    arena: &TermArena,
    term: TermId,
    bound: &BTreeSet<SymbolId>,
    free: &BTreeMap<SymbolId, Value>,
) -> Truth {
    match arena.node(term) {
        TermNode::BoolConst(value) => Truth::from(*value),
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [arg]) => negate(prove_bool(arena, *arg, bound, free)),
            (Op::BoolAnd, [left, right]) => and(
                prove_bool(arena, *left, bound, free),
                prove_bool(arena, *right, bound, free),
            ),
            (Op::BoolOr, [left, right]) => or(
                prove_bool(arena, *left, bound, free),
                prove_bool(arena, *right, bound, free),
            ),
            (Op::BoolImplies, [left, right]) => or(
                negate(prove_bool(arena, *left, bound, free)),
                prove_bool(arena, *right, bound, free),
            ),
            (Op::Eq, [left, right]) if left == right => Truth::True,
            (Op::Eq, [left, right])
                if matches!(arena.sort_of(*left), Sort::BitVec(_))
                    && arena.sort_of(*left) == arena.sort_of(*right) =>
            {
                match (
                    affine_lsb(arena, *left, bound, free),
                    affine_lsb(arena, *right, bound, free),
                ) {
                    (Some(left), Some(right))
                        if left.variables == right.variables && left.constant != right.constant =>
                    {
                        Truth::False
                    }
                    _ => Truth::Unknown,
                }
            }
            _ => Truth::Unknown,
        },
        _ => Truth::Unknown,
    }
}

impl From<bool> for Truth {
    fn from(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }
}

fn negate(value: Truth) -> Truth {
    match value {
        Truth::False => Truth::True,
        Truth::Unknown => Truth::Unknown,
        Truth::True => Truth::False,
    }
}

fn and(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::False, _) | (_, Truth::False) => Truth::False,
        (Truth::True, Truth::True) => Truth::True,
        _ => Truth::Unknown,
    }
}

fn or(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::True, _) | (_, Truth::True) => Truth::True,
        (Truth::False, Truth::False) => Truth::False,
        _ => Truth::Unknown,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AffineLsb {
    variables: BTreeSet<SymbolId>,
    constant: bool,
}

impl AffineLsb {
    fn constant(value: bool) -> Self {
        Self {
            variables: BTreeSet::new(),
            constant: value,
        }
    }

    fn xor(mut self, other: Self) -> Self {
        for variable in other.variables {
            if !self.variables.insert(variable) {
                self.variables.remove(&variable);
            }
        }
        self.constant ^= other.constant;
        self
    }
}

fn affine_lsb(
    arena: &TermArena,
    term: TermId,
    bound: &BTreeSet<SymbolId>,
    free: &BTreeMap<SymbolId, Value>,
) -> Option<AffineLsb> {
    match arena.node(term) {
        TermNode::BvConst { value, .. } => Some(AffineLsb::constant(value & 1 == 1)),
        TermNode::WideBvConst(value) => Some(AffineLsb::constant(value.bit(0))),
        TermNode::Symbol(symbol) if bound.contains(symbol) => Some(AffineLsb {
            variables: BTreeSet::from([*symbol]),
            constant: false,
        }),
        TermNode::Symbol(symbol) => free
            .get(symbol)
            .and_then(value_lsb)
            .map(AffineLsb::constant),
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BvNeg | Op::ZeroExt { .. } | Op::SignExt { .. }, [arg]) => {
                affine_lsb(arena, *arg, bound, free)
            }
            (Op::BvNot, [arg]) => affine_lsb(arena, *arg, bound, free)
                .map(|value| value.xor(AffineLsb::constant(true))),
            (Op::BvAdd | Op::BvSub | Op::BvXor, [left, right]) => Some(
                affine_lsb(arena, *left, bound, free)?.xor(affine_lsb(arena, *right, bound, free)?),
            ),
            (Op::BvMul, [left, right]) => {
                let left = affine_lsb(arena, *left, bound, free)?;
                let right = affine_lsb(arena, *right, bound, free)?;
                if left.variables.is_empty() {
                    Some(if left.constant {
                        right
                    } else {
                        AffineLsb::constant(false)
                    })
                } else if right.variables.is_empty() {
                    Some(if right.constant {
                        left
                    } else {
                        AffineLsb::constant(false)
                    })
                } else {
                    None
                }
            }
            (Op::Extract { lo: 0, .. }, [arg]) => affine_lsb(arena, *arg, bound, free),
            (Op::Concat, [_high, low]) => affine_lsb(arena, *low, bound, free),
            _ => None,
        },
        _ => None,
    }
}

fn value_lsb(value: &Value) -> Option<bool> {
    match value {
        Value::Bv { value, .. } => Some(value & 1 == 1),
        Value::WideBv(value) => Some(value.bit(0)),
        _ => None,
    }
}

fn contains_quantifier(arena: &TermArena, root: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

pub(crate) fn admitted_free_bv_symbols(arena: &TermArena, root: TermId) -> Option<Vec<SymbolId>> {
    source_shape(arena, root).map(|shape| shape.free)
}

pub(crate) fn direct_negated_universal(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(Vec<SymbolId>, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(assertion)
    else {
        return None;
    };
    let [inner] = &**args else { return None };
    let (binders, body) = peel_prefix(arena, *inner, true)?;
    (!binders.is_empty() && !contains_quantifier(arena, body)).then_some((binders, body))
}
