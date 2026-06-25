//! Bounded Bool/BV enumeration modulo checked top-level definitions.
//!
//! This certificate is narrower than a solver and broader than raw term-level
//! enumeration. It uses only constraints that are required by the original query:
//! top-level conjunctions, plus the antecedent of a top-level `not (=> a b)`.
//! Equalities of the form `x = t` define `x`; small domain constraints such as
//! `x < p` and `x = 0 or x = 1` shrink independent domains. The checker then
//! enumerates every independent assignment, extends it with the definitions, and
//! replays the original assertions with the trusted evaluator.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

const MAX_SYMBOL_WIDTH: u32 = 16;
const MAX_CASES: u64 = 1_000_000;

/// A self-checking Bool/BV refutation by exhaustive enumeration after applying
/// required top-level symbol definitions and finite-domain restrictions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvDefinedEnumRefutationCertificate {
    /// Number of independent assignments evaluated.
    pub cases: u64,
    /// Independent symbols enumerated, in deterministic symbol order.
    pub independent_symbols: Vec<SymbolId>,
    /// Symbols whose values were computed from required top-level equalities.
    pub defined_symbols: Vec<SymbolId>,
    /// Independent symbols whose domains were restricted by required constraints.
    pub restricted_symbols: Vec<SymbolId>,
}

#[derive(Debug, Clone)]
struct Definition {
    symbol: SymbolId,
    sort: Sort,
    expr: TermId,
}

#[derive(Debug, Clone)]
struct EnumSymbol {
    symbol: SymbolId,
    domain: Vec<Value>,
    full_len: usize,
}

/// Returns a certificate when all satisfying assignments are covered by bounded
/// definition-aware enumeration and every covered assignment falsifies the
/// original assertions.
#[must_use]
pub fn bv_defined_enum_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BvDefinedEnumRefutationCertificate> {
    if assertions.is_empty()
        || assertions
            .iter()
            .any(|&assertion| !is_pure_bool_bv_term(arena, assertion))
    {
        return None;
    }

    let mut required = Vec::new();
    for &assertion in assertions {
        collect_required_constraints(arena, assertion, &mut required);
    }

    let symbol_sorts = collect_symbol_sorts(arena, assertions)?;
    if symbol_sorts.is_empty() {
        return None;
    }
    let definitions = collect_definitions(arena, &required);
    let defined_symbols: BTreeSet<_> = definitions.iter().map(|d| d.symbol).collect();
    if definitions.is_empty() || defined_symbols.len() == symbol_sorts.len() {
        return None;
    }

    let enum_symbols = independent_domains(arena, &required, &symbol_sorts, &defined_symbols)?;
    let cases = enum_symbols.iter().try_fold(1_u64, |acc, symbol| {
        acc.checked_mul(u64::try_from(symbol.domain.len()).ok()?)
    })?;
    if cases == 0 || cases > MAX_CASES {
        return None;
    }

    if !all_cases_refute(arena, assertions, &definitions, &enum_symbols, cases)? {
        return None;
    }

    Some(BvDefinedEnumRefutationCertificate {
        cases,
        independent_symbols: enum_symbols.iter().map(|s| s.symbol).collect(),
        defined_symbols: definitions.iter().map(|d| d.symbol).collect(),
        restricted_symbols: enum_symbols
            .iter()
            .filter(|s| s.domain.len() < s.full_len)
            .map(|s| s.symbol)
            .collect(),
    })
}

fn collect_required_constraints(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 => {
            collect_required_constraints(arena, args[0], out);
            collect_required_constraints(arena, args[1], out);
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => {
            if let TermNode::App {
                op: Op::BoolImplies,
                args: inner_args,
            } = arena.node(args[0])
                && inner_args.len() == 2
            {
                collect_required_constraints(arena, inner_args[0], out);
                return;
            }
            out.push(term);
        }
        _ => out.push(term),
    }
}

fn collect_symbol_sorts(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BTreeMap<SymbolId, Sort>> {
    let mut out = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                let sort = arena.sort_of(term);
                if !small_enum_sort(sort) {
                    return None;
                }
                out.insert(*symbol, sort);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    Some(out)
}

fn collect_definitions(arena: &TermArena, required: &[TermId]) -> Vec<Definition> {
    let mut out = BTreeMap::<SymbolId, Definition>::new();
    for &constraint in required {
        let Some((lhs, rhs)) = match_equality(arena, constraint) else {
            continue;
        };
        let Some(definition) = definition_from_equality(arena, lhs, rhs)
            .or_else(|| definition_from_equality(arena, rhs, lhs))
        else {
            continue;
        };
        out.entry(definition.symbol).or_insert(definition);
    }
    out.into_values().collect()
}

fn definition_from_equality(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<Definition> {
    let TermNode::Symbol(symbol) = arena.node(lhs) else {
        return None;
    };
    let sort = arena.sort_of(lhs);
    if arena.sort_of(rhs) != sort
        || !small_enum_sort(sort)
        || contains_symbol(arena, rhs, *symbol)
        || !is_pure_bool_bv_term(arena, rhs)
    {
        return None;
    }
    Some(Definition {
        symbol: *symbol,
        sort,
        expr: rhs,
    })
}

fn independent_domains(
    arena: &TermArena,
    required: &[TermId],
    symbol_sorts: &BTreeMap<SymbolId, Sort>,
    defined_symbols: &BTreeSet<SymbolId>,
) -> Option<Vec<EnumSymbol>> {
    let mut domains = BTreeMap::new();
    for (&symbol, &sort) in symbol_sorts {
        if defined_symbols.contains(&symbol) {
            continue;
        }
        let domain = full_domain(sort)?;
        domains.insert(
            symbol,
            EnumSymbol {
                symbol,
                full_len: domain.len(),
                domain,
            },
        );
    }

    for &constraint in required {
        if let Some((symbol, allowed)) = match_finite_domain_constraint(arena, constraint) {
            apply_restriction(&mut domains, symbol, &allowed);
        }
    }

    let out: Vec<_> = domains.into_values().collect();
    if out.iter().any(|symbol| symbol.domain.is_empty()) {
        return None;
    }
    Some(out)
}

fn match_finite_domain_constraint(
    arena: &TermArena,
    constraint: TermId,
) -> Option<(SymbolId, Vec<Value>)> {
    if let Some((symbol, value)) = match_symbol_constant_equality(arena, constraint) {
        return Some((symbol, vec![value]));
    }
    if let Some((symbol, values)) = match_symbol_constant_or(arena, constraint) {
        return Some((symbol, values));
    }
    match_bv_range(arena, constraint)
}

fn match_symbol_constant_or(arena: &TermArena, term: TermId) -> Option<(SymbolId, Vec<Value>)> {
    let mut leaves = Vec::new();
    collect_or_leaves(arena, term, &mut leaves);
    if leaves.len() < 2 {
        return None;
    }
    let mut symbol = None;
    let mut values = Vec::new();
    for leaf in leaves {
        let (leaf_symbol, value) = match_symbol_constant_equality(arena, leaf)?;
        if symbol.is_some_and(|s| s != leaf_symbol) {
            return None;
        }
        symbol = Some(leaf_symbol);
        if !values.contains(&value) {
            values.push(value);
        }
    }
    Some((symbol?, values))
}

fn collect_or_leaves(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolOr,
            args,
        } if args.len() == 2 => {
            collect_or_leaves(arena, args[0], out);
            collect_or_leaves(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn match_symbol_constant_equality(arena: &TermArena, term: TermId) -> Option<(SymbolId, Value)> {
    let (lhs, rhs) = match_equality(arena, term)?;
    symbol_constant_side(arena, lhs, rhs).or_else(|| symbol_constant_side(arena, rhs, lhs))
}

fn symbol_constant_side(
    arena: &TermArena,
    symbol_term: TermId,
    const_term: TermId,
) -> Option<(SymbolId, Value)> {
    let TermNode::Symbol(symbol) = arena.node(symbol_term) else {
        return None;
    };
    let value = constant_value(arena, const_term)?;
    value_matches_sort(arena.sort_of(symbol_term), &value).then_some((*symbol, value))
}

fn match_bv_range(arena: &TermArena, term: TermId) -> Option<(SymbolId, Vec<Value>)> {
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if !matches!(op, Op::BvUlt | Op::BvUle) || args.len() != 2 {
        return None;
    }
    let TermNode::Symbol(symbol) = arena.node(args[0]) else {
        return None;
    };
    let Sort::BitVec(width) = arena.sort_of(args[0]) else {
        return None;
    };
    let TermNode::BvConst {
        width: const_width,
        value,
    } = arena.node(args[1])
    else {
        return None;
    };
    if *const_width != width || width > MAX_SYMBOL_WIDTH {
        return None;
    }
    let upper = match op {
        Op::BvUlt => *value,
        Op::BvUle => value.checked_add(1)?,
        _ => unreachable!("range op already matched"),
    };
    let limit = upper.min(1_u128.checked_shl(width).unwrap_or(0));
    let mut values = Vec::new();
    for value in 0..limit {
        values.push(Value::Bv { width, value });
    }
    Some((*symbol, values))
}

fn apply_restriction(
    domains: &mut BTreeMap<SymbolId, EnumSymbol>,
    symbol: SymbolId,
    allowed: &[Value],
) {
    if let Some(domain) = domains.get_mut(&symbol) {
        domain.domain.retain(|value| allowed.contains(value));
    }
}

fn all_cases_refute(
    arena: &TermArena,
    assertions: &[TermId],
    definitions: &[Definition],
    enum_symbols: &[EnumSymbol],
    cases: u64,
) -> Option<bool> {
    for case in 0..cases {
        let mut assignment = decode_assignment(enum_symbols, case)?;
        apply_definitions(arena, definitions, &mut assignment)?;
        if all_assertions_true(arena, assertions, &assignment)? {
            return Some(false);
        }
    }
    Some(true)
}

fn decode_assignment(enum_symbols: &[EnumSymbol], mut code: u64) -> Option<Assignment> {
    let mut assignment = Assignment::new();
    for symbol in enum_symbols {
        let radix = u64::try_from(symbol.domain.len()).ok()?;
        let idx = usize::try_from(code % radix).ok()?;
        code /= radix;
        assignment.set(symbol.symbol, symbol.domain[idx].clone());
    }
    Some(assignment)
}

fn apply_definitions(
    arena: &TermArena,
    definitions: &[Definition],
    assignment: &mut Assignment,
) -> Option<()> {
    let mut pending: Vec<_> = definitions.iter().collect();
    while !pending.is_empty() {
        let mut next = Vec::new();
        let mut progressed = false;
        for definition in pending {
            match eval(arena, definition.expr, assignment) {
                Ok(value) if value_matches_sort(definition.sort, &value) => {
                    assignment.set(definition.symbol, value);
                    progressed = true;
                }
                _ => next.push(definition),
            }
        }
        if !progressed {
            return None;
        }
        pending = next;
    }
    Some(())
}

fn all_assertions_true(
    arena: &TermArena,
    assertions: &[TermId],
    assignment: &Assignment,
) -> Option<bool> {
    for &assertion in assertions {
        match eval(arena, assertion, assignment).ok()? {
            Value::Bool(true) => {}
            Value::Bool(false) => return Some(false),
            _ => return None,
        }
    }
    Some(true)
}

fn match_equality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn constant_value(arena: &TermArena, term: TermId) -> Option<Value> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(Value::Bool(*value)),
        TermNode::BvConst { width, value } => Some(Value::Bv {
            width: *width,
            value: *value,
        }),
        _ => None,
    }
}

fn full_domain(sort: Sort) -> Option<Vec<Value>> {
    match sort {
        Sort::Bool => Some(vec![Value::Bool(false), Value::Bool(true)]),
        Sort::BitVec(width) if width <= MAX_SYMBOL_WIDTH => {
            let count = 1_u128.checked_shl(width)?;
            let mut values = Vec::new();
            for value in 0..count {
                values.push(Value::Bv { width, value });
            }
            Some(values)
        }
        _ => None,
    }
}

fn small_enum_sort(sort: Sort) -> bool {
    match sort {
        Sort::Bool => true,
        Sort::BitVec(width) => width <= MAX_SYMBOL_WIDTH,
        _ => false,
    }
}

fn value_matches_sort(sort: Sort, value: &Value) -> bool {
    match (sort, value) {
        (Sort::Bool, Value::Bool(_)) => true,
        (
            Sort::BitVec(width),
            Value::Bv {
                width: value_width, ..
            },
        ) => width == *value_width,
        _ => false,
    }
}

fn contains_symbol(arena: &TermArena, term: TermId, target: SymbolId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(next) = stack.pop() {
        if !seen.insert(next) {
            continue;
        }
        match arena.node(next) {
            TermNode::Symbol(symbol) if *symbol == target => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

fn is_pure_bool_bv_term(arena: &TermArena, term: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(next) = stack.pop() {
        if !seen.insert(next) {
            continue;
        }
        match arena.node(next) {
            TermNode::BoolConst(_) | TermNode::BvConst { .. } | TermNode::WideBvConst(_) => {}
            TermNode::Symbol(_) if matches!(arena.sort_of(next), Sort::Bool | Sort::BitVec(_)) => {}
            TermNode::App { op, args } if is_pure_bool_bv_op(*op) => {
                stack.extend(args.iter().copied());
            }
            _ => return false,
        }
    }
    true
}

fn is_pure_bool_bv_op(op: Op) -> bool {
    matches!(
        op,
        Op::BoolNot
            | Op::BoolAnd
            | Op::BoolOr
            | Op::BoolXor
            | Op::BoolImplies
            | Op::BvNot
            | Op::BvAnd
            | Op::BvOr
            | Op::BvXor
            | Op::BvNand
            | Op::BvNor
            | Op::BvXnor
            | Op::BvNeg
            | Op::BvAdd
            | Op::BvSub
            | Op::BvMul
            | Op::BvUdiv
            | Op::BvUrem
            | Op::BvSdiv
            | Op::BvSrem
            | Op::BvSmod
            | Op::BvShl
            | Op::BvLshr
            | Op::BvAshr
            | Op::BvUlt
            | Op::BvUle
            | Op::BvUgt
            | Op::BvUge
            | Op::BvSlt
            | Op::BvSle
            | Op::BvSgt
            | Op::BvSge
            | Op::Eq
            | Op::Ite
            | Op::BvComp
            | Op::Extract { .. }
            | Op::Concat
            | Op::ZeroExt { .. }
            | Op::SignExt { .. }
            | Op::RotateLeft { .. }
            | Op::RotateRight { .. }
    )
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::bv_defined_enum_refutation;

    #[test]
    fn certifies_finite_field_mac_identity() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean/cli__regress0__ff__issue10937.smt2"
        ))
        .expect("issue10937 parses");
        let cert = bv_defined_enum_refutation(&script.arena, &script.assertions)
            .expect("definition-aware enumeration certifies issue10937");
        assert_eq!(cert.cases, 16_807);
        assert_eq!(cert.defined_symbols.len(), 2);
        assert_eq!(cert.independent_symbols.len(), 5);
    }

    #[test]
    fn certifies_finite_field_xor_soundness() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean/cli__regress0__ff__ff_xor_sound.smt2"
        ))
        .expect("ff_xor_sound parses");
        let cert = bv_defined_enum_refutation(&script.arena, &script.assertions)
            .expect("definition-aware enumeration certifies xor soundness");
        assert!(cert.cases <= 20_000);
        assert!(!cert.defined_symbols.is_empty());
        assert!(cert.restricted_symbols.len() >= 7);
    }
}
