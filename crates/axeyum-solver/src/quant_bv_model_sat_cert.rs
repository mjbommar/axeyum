//! Source-bound quantified-BV model certificates (ADR-0130/0131).
//!
//! Candidate search is deliberately outside this module. The checker below
//! proves an untouched assertion under a complete free-BV assignment by either
//! an affine least-significant-bit invariant, a concrete counterexample to a
//! directly negated universal, exact signed-interval containment, or exact
//! zero-product annihilation below a directly negated existential implication.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{
    Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, WideUint, eval,
};

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
    /// A directly negated existential implication is false at every binder
    /// value because its ground facts hold, its ground conclusion is false,
    /// and its sole binder-dependent interval implication is contained.
    NegatedExistentialIntervalImplication {
        /// The single existential binder named by the untouched source.
        binder: SymbolId,
    },
    /// A directly negated existential implication is false at every binder
    /// value because an exact ground-zero signed-division factor annihilates
    /// the sole binder-dependent product obligation.
    NegatedExistentialZeroProductImplication {
        /// The single existential binder named by the untouched source.
        binder: SymbolId,
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
        QuantifiedBvModelSatProof::NegatedExistentialIntervalImplication { binder } => {
            check_negated_existential_interval_implication(
                arena,
                assertion,
                &shape,
                &free_values,
                *binder,
            )
        }
        QuantifiedBvModelSatProof::NegatedExistentialZeroProductImplication { binder } => {
            check_negated_existential_zero_product_implication(
                arena,
                assertion,
                &shape,
                &free_values,
                *binder,
            )
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

fn check_negated_existential_interval_implication(
    arena: &TermArena,
    assertion: TermId,
    source: &SourceShape,
    free: &BTreeMap<SymbolId, Value>,
    claimed_binder: SymbolId,
) -> bool {
    let Some(shape) = negated_existential_interval_shape(arena, assertion) else {
        return false;
    };
    let mut assignment = Assignment::new();
    for (&symbol, value) in free {
        assignment.set(symbol, value.clone());
    }
    if shape.binder != claimed_binder
        || source.binders != BTreeSet::from([shape.binder])
        || shape
            .ground_true
            .iter()
            .any(|&term| !eval_bool(arena, term, &assignment, true))
        || !eval_bool(arena, shape.ground_false, &assignment, false)
    {
        return false;
    }
    let Some(lower) = eval_bv(arena, shape.lower, &assignment) else {
        return false;
    };
    let Some(upper) = eval_bv(arena, shape.upper, &assignment) else {
        return false;
    };
    let Some(cap) = eval_bv(arena, shape.cap, &assignment) else {
        return false;
    };

    // Deliberately reject empty intervals: vacuity is not evidence for this
    // certificate. The two comparisons prove [lower, upper] is nonempty and
    // contained in (-infinity, cap] in signed two's-complement order.
    signed_le(&lower, &upper) && signed_le(&upper, &cap)
}

fn check_negated_existential_zero_product_implication(
    arena: &TermArena,
    assertion: TermId,
    source: &SourceShape,
    free: &BTreeMap<SymbolId, Value>,
    claimed_binder: SymbolId,
) -> bool {
    let Some(shape) = negated_existential_zero_product_shape(arena, assertion) else {
        return false;
    };
    let mut assignment = Assignment::new();
    for (&symbol, value) in free {
        assignment.set(symbol, value.clone());
    }
    if shape.binder != claimed_binder
        || source.binders != BTreeSet::from([shape.binder])
        || shape
            .ground_true
            .iter()
            .any(|&term| !eval_bool(arena, term, &assignment, true))
        || !eval_bool(arena, shape.ground_false, &assignment, false)
    {
        return false;
    }
    eval_bv(arena, shape.zero_factor, &assignment).is_some_and(|value| match value {
        Value::Bv { value, .. } => value == 0,
        Value::WideBv(value) => value.is_zero(),
        _ => false,
    })
}

fn eval_bool(arena: &TermArena, term: TermId, assignment: &Assignment, expected: bool) -> bool {
    matches!(eval(arena, term, assignment), Ok(Value::Bool(value)) if value == expected)
}

fn eval_bv(arena: &TermArena, term: TermId, assignment: &Assignment) -> Option<Value> {
    match eval(arena, term, assignment).ok()? {
        value @ (Value::Bv { .. } | Value::WideBv(_)) => Some(value),
        _ => None,
    }
}

fn signed_le(left: &Value, right: &Value) -> bool {
    let widen = |value: &Value| match value {
        Value::Bv { width, value } => Some(WideUint::from_u128(*value, *width)),
        Value::WideBv(value) => Some(value.clone()),
        _ => None,
    };
    let (Some(left), Some(right)) = (widen(left), widen(right)) else {
        return false;
    };
    left.width() == right.width() && left.sle(&right)
}

#[derive(Debug, Clone)]
pub(crate) struct NegatedExistentialIntervalShape {
    pub binder: SymbolId,
    pub ground_true: Vec<TermId>,
    pub lower: TermId,
    pub upper: TermId,
    pub cap: TermId,
    pub ground_false: TermId,
}

pub(crate) fn negated_existential_interval_shape(
    arena: &TermArena,
    assertion: TermId,
) -> Option<NegatedExistentialIntervalShape> {
    let (binder, conjuncts, ground_false) =
        direct_negated_existential_implication(arena, assertion)?;
    let mut ground_true = Vec::new();
    let mut interval = None;
    for conjunct in conjuncts {
        if contains_symbol(arena, conjunct, binder) {
            if interval.is_some() {
                return None;
            }
            interval = Some(parse_interval_implication(arena, conjunct, binder)?);
        } else {
            ground_true.push(conjunct);
        }
    }
    let (lower, upper, cap, mut interval_ground) = interval?;
    ground_true.append(&mut interval_ground);
    Some(NegatedExistentialIntervalShape {
        binder,
        ground_true,
        lower,
        upper,
        cap,
        ground_false,
    })
}

#[derive(Debug, Clone)]
pub(crate) struct NegatedExistentialZeroProductShape {
    pub binder: SymbolId,
    pub ground_true: Vec<TermId>,
    pub zero_factor: TermId,
    pub ground_false: TermId,
}

pub(crate) fn negated_existential_zero_product_shape(
    arena: &TermArena,
    assertion: TermId,
) -> Option<NegatedExistentialZeroProductShape> {
    let (binder, conjuncts, ground_false) =
        direct_negated_existential_implication(arena, assertion)?;
    let mut ground_true = Vec::new();
    let mut zero_factor = None;
    for conjunct in conjuncts {
        if contains_symbol(arena, conjunct, binder) {
            if zero_factor.is_some() {
                return None;
            }
            zero_factor = Some(parse_zero_product_implication(arena, conjunct, binder)?);
        } else {
            ground_true.push(conjunct);
        }
    }
    Some(NegatedExistentialZeroProductShape {
        binder,
        ground_true,
        zero_factor: zero_factor?,
        ground_false,
    })
}

fn direct_negated_existential_implication(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(SymbolId, Vec<TermId>, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(assertion)
    else {
        return None;
    };
    let [inner] = &**args else { return None };
    let (binders, body) = peel_prefix(arena, *inner, false)?;
    let [binder] = binders.as_slice() else {
        return None;
    };
    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [antecedent, ground_false] = &**args else {
        return None;
    };
    if contains_symbol(arena, *ground_false, *binder) {
        return None;
    }
    let mut conjuncts = Vec::new();
    flatten_and(arena, *antecedent, &mut conjuncts);
    Some((*binder, conjuncts, *ground_false))
}

fn parse_zero_product_implication(
    arena: &TermArena,
    term: TermId,
    binder: SymbolId,
) -> Option<TermId> {
    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [_premise, conclusion] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::BvSge,
        args,
    } = arena.node(*conclusion)
    else {
        return None;
    };
    let [product, zero] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::BvMul,
        args,
    } = arena.node(*product)
    else {
        return None;
    };
    let [left, right] = &**args else { return None };
    let zero_factor = if is_direct_ground_sdiv(arena, *left, binder)
        && contains_symbol(arena, *right, binder)
    {
        *left
    } else if is_direct_ground_sdiv(arena, *right, binder) && contains_symbol(arena, *left, binder)
    {
        *right
    } else {
        return None;
    };
    let binder_sort = arena.symbol(binder).1;
    (matches!(binder_sort, Sort::BitVec(_))
        && arena.sort_of(zero_factor) == binder_sort
        && arena.sort_of(*product) == binder_sort
        && arena.sort_of(*zero) == binder_sort
        && is_bv_zero_literal(arena, *zero))
    .then_some(zero_factor)
}

fn is_direct_ground_sdiv(arena: &TermArena, term: TermId, binder: SymbolId) -> bool {
    matches!(
        arena.node(term),
        TermNode::App { op: Op::BvSdiv, args }
            if args.len() == 2 && !contains_symbol(arena, term, binder)
    )
}

fn is_bv_zero_literal(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::BvConst { value, .. } => *value == 0,
        TermNode::WideBvConst(value) => value.is_zero(),
        _ => false,
    }
}

fn parse_interval_implication(
    arena: &TermArena,
    term: TermId,
    binder: SymbolId,
) -> Option<(TermId, TermId, TermId, Vec<TermId>)> {
    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [range, conclusion] = &**args else {
        return None;
    };
    let mut bounds = Vec::new();
    flatten_and(arena, *range, &mut bounds);
    if bounds.len() != 2 {
        return None;
    }
    let mut lower = None;
    let mut upper = None;
    for bound in bounds {
        let TermNode::App {
            op: Op::BvSle,
            args,
        } = arena.node(bound)
        else {
            return None;
        };
        let [left, right] = &**args else { return None };
        if is_symbol(arena, *right, binder) && !contains_symbol(arena, *left, binder) {
            if lower.replace(*left).is_some() {
                return None;
            }
        } else if is_symbol(arena, *left, binder) && !contains_symbol(arena, *right, binder) {
            if upper.replace(*right).is_some() {
                return None;
            }
        } else {
            return None;
        }
    }

    let mut conclusion_terms = Vec::new();
    flatten_and(arena, *conclusion, &mut conclusion_terms);
    let mut cap = None;
    let mut ground = Vec::new();
    for item in conclusion_terms {
        if contains_symbol(arena, item, binder) {
            let TermNode::App {
                op: Op::BvSle,
                args,
            } = arena.node(item)
            else {
                return None;
            };
            let [left, right] = &**args else { return None };
            if !is_symbol(arena, *left, binder)
                || contains_symbol(arena, *right, binder)
                || cap.replace(*right).is_some()
            {
                return None;
            }
        } else {
            ground.push(item);
        }
    }
    let (lower, upper, cap) = (lower?, upper?, cap?);
    let sort = arena.symbol(binder).1;
    if !matches!(sort, Sort::BitVec(_))
        || arena.sort_of(lower) != sort
        || arena.sort_of(upper) != sort
        || arena.sort_of(cap) != sort
    {
        return None;
    }
    Some((lower, upper, cap, ground))
}

fn flatten_and(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        flatten_and(arena, *left, out);
        flatten_and(arena, *right, out);
    } else {
        out.push(term);
    }
}

fn is_symbol(arena: &TermArena, term: TermId, symbol: SymbolId) -> bool {
    matches!(arena.node(term), TermNode::Symbol(actual) if *actual == symbol)
}

fn contains_symbol(arena: &TermArena, root: TermId, symbol: SymbolId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(actual) if *actual == symbol => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
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
