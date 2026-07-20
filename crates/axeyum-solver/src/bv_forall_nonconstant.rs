//! Checked refutations for small quantified-BV inversion benchmarks.
//!
//! The accepted formulas assert that a visibly non-constant BV expression is
//! equal to one fixed BV term for every value of its quantified variable, for
//! example `forall x. bvadd x a = b`. Each accepted schema has two concrete
//! witnesses for the quantified variable that force incompatible values for the
//! fixed result. The matcher is deliberately narrow and re-checkable over the
//! original IR; it is not a quantifier solver.

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

/// The checked quantified-BV schema used by a refutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BvForallNonconstantKind {
    /// `forall x. bvadd x a = b`; witnesses `x=0` and `x=1`.
    BvAdd,
    /// `forall x. bvashr x a = b`; witnesses `x=0` and `x=allones`.
    BvAshr,
    /// `forall x. concat x a = b`; witnesses two different high halves.
    ConcatHigh,
    /// `forall x. concat a x = b`; witnesses two different low halves.
    ConcatLow,
    /// `a != 0`, `b != 0`, and `forall x. bvudiv x a = b`; witness `x=0`.
    BvUdivDividend,
    /// `a != b` and `forall x. bvudiv a x = b`; witness `x=1`.
    BvUdivDivisor,
}

/// A self-checking refutation of a universal BV equality whose left side cannot
/// be constant over the quantified domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BvForallNonconstantRefutationCertificate {
    /// The original top-level universal assertion.
    pub assertion: TermId,
    /// The quantified symbol.
    pub variable: SymbolId,
    /// The varying operator schema.
    pub kind: BvForallNonconstantKind,
    /// The non-quantified operand paired with the quantified variable.
    pub parameter: TermId,
    /// The fixed result term the universal equality tries to force.
    pub result: TermId,
    /// Bit-width of the quantified variable.
    pub variable_width: u32,
}

/// Returns a certificate when the assertions contain one of the checked
/// quantified-BV non-constant schemas.
#[must_use]
pub fn bv_forall_nonconstant_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BvForallNonconstantRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    for &assertion in &conjuncts {
        if let Some(cert) = match_forall_nonconstant(arena, assertion, &conjuncts) {
            return Some(cert);
        }
    }
    None
}

fn match_forall_nonconstant(
    arena: &TermArena,
    assertion: TermId,
    conjuncts: &[TermId],
) -> Option<BvForallNonconstantRefutationCertificate> {
    let TermNode::App {
        op: Op::Forall(variable),
        args,
    } = arena.node(assertion)
    else {
        return None;
    };
    let [body] = &**args else {
        return None;
    };
    let Sort::BitVec(variable_width) = arena.symbol(*variable).1 else {
        return None;
    };
    if variable_width == 0 {
        return None;
    }
    let (varying, result) = match_eq_with_fixed_result(arena, *body, *variable)?;
    let TermNode::App { op, args } = arena.node(varying) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let (kind, parameter) = match op {
        Op::BvAdd => {
            let parameter = match_one_bound_operand(arena, *left, *right, *variable)?;
            (BvForallNonconstantKind::BvAdd, parameter)
        }
        Op::BvAshr
            if is_symbol(arena, *left, *variable) && !contains_symbol(arena, *right, *variable) =>
        {
            (BvForallNonconstantKind::BvAshr, *right)
        }
        Op::Concat
            if is_symbol(arena, *left, *variable) && !contains_symbol(arena, *right, *variable) =>
        {
            (BvForallNonconstantKind::ConcatHigh, *right)
        }
        Op::Concat
            if is_symbol(arena, *right, *variable) && !contains_symbol(arena, *left, *variable) =>
        {
            (BvForallNonconstantKind::ConcatLow, *left)
        }
        Op::BvUdiv
            if is_symbol(arena, *left, *variable) && !contains_symbol(arena, *right, *variable) =>
        {
            let zero = find_bv_zero(arena, conjuncts, arena.sort_of(*right))?;
            if !has_disequality(arena, conjuncts, *right, zero)
                || !has_disequality(arena, conjuncts, result, zero)
            {
                return None;
            }
            (BvForallNonconstantKind::BvUdivDividend, *right)
        }
        Op::BvUdiv
            if is_symbol(arena, *right, *variable) && !contains_symbol(arena, *left, *variable) =>
        {
            if !has_disequality(arena, conjuncts, *left, result) {
                return None;
            }
            (BvForallNonconstantKind::BvUdivDivisor, *left)
        }
        _ => return None,
    };

    Some(BvForallNonconstantRefutationCertificate {
        assertion,
        variable: *variable,
        kind,
        parameter,
        result,
        variable_width,
    })
}

fn match_eq_with_fixed_result(
    arena: &TermArena,
    body: TermId,
    variable: SymbolId,
) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(body) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    let lhs_has = contains_symbol(arena, *lhs, variable);
    let rhs_has = contains_symbol(arena, *rhs, variable);
    match (lhs_has, rhs_has) {
        (true, false) => Some((*lhs, *rhs)),
        (false, true) => Some((*rhs, *lhs)),
        _ => None,
    }
}

fn match_one_bound_operand(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    variable: SymbolId,
) -> Option<TermId> {
    if is_symbol(arena, left, variable) && !contains_symbol(arena, right, variable) {
        Some(right)
    } else if is_symbol(arena, right, variable) && !contains_symbol(arena, left, variable) {
        Some(left)
    } else {
        None
    }
}

fn has_disequality(arena: &TermArena, conjuncts: &[TermId], lhs: TermId, rhs: TermId) -> bool {
    conjuncts.iter().copied().any(|term| {
        match_disequality(arena, term)
            .is_some_and(|(a, b)| (a == lhs && b == rhs) || (a == rhs && b == lhs))
    })
}

fn match_disequality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*inner) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn find_bv_zero(arena: &TermArena, conjuncts: &[TermId], sort: Sort) -> Option<TermId> {
    conjuncts
        .iter()
        .copied()
        .flat_map(|term| disequality_terms(arena, term))
        .find(|&term| arena.sort_of(term) == sort && is_bv_zero(arena, term))
}

fn disequality_terms(arena: &TermArena, term: TermId) -> [TermId; 2] {
    match match_disequality(arena, term) {
        Some((lhs, rhs)) => [lhs, rhs],
        None => [term, term],
    }
}

fn is_symbol(arena: &TermArena, term: TermId, symbol: SymbolId) -> bool {
    matches!(arena.node(term), TermNode::Symbol(found) if *found == symbol)
}

fn is_bv_zero(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::BvConst { value, .. } => *value == 0,
        TermNode::WideBvConst(value) => value.is_zero(),
        _ => false,
    }
}

fn contains_symbol(arena: &TermArena, term: TermId, symbol: SymbolId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        match arena.node(current) {
            TermNode::Symbol(found) if *found == symbol => return true,
            TermNode::App {
                op: Op::Forall(bound) | Op::Exists(bound),
                ..
            } if *bound == symbol => {}
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::{BvForallNonconstantKind, bv_forall_nonconstant_refutation};

    #[test]
    fn recognizes_bvadd_universal_nonconstant() {
        let script = parse_script(
            r"
            (set-logic BV)
            (declare-fun a () (_ BitVec 8))
            (declare-fun b () (_ BitVec 8))
            (assert (forall ((x (_ BitVec 8))) (= (bvadd x a) b)))
            (check-sat)
        ",
        )
        .unwrap();
        let cert = bv_forall_nonconstant_refutation(&script.arena, &script.assertions).unwrap();
        assert_eq!(cert.kind, BvForallNonconstantKind::BvAdd);
        assert_eq!(cert.variable_width, 8);
    }

    #[test]
    fn recognizes_guarded_bvudiv_dividend() {
        let script = parse_script(
            r"
            (set-logic BV)
            (declare-fun a () (_ BitVec 8))
            (declare-fun b () (_ BitVec 8))
            (assert (distinct a b (_ bv0 8)))
            (assert (forall ((x (_ BitVec 8))) (= (bvudiv x a) b)))
            (check-sat)
        ",
        )
        .unwrap();
        let cert = bv_forall_nonconstant_refutation(&script.arena, &script.assertions).unwrap();
        assert_eq!(cert.kind, BvForallNonconstantKind::BvUdivDividend);
    }

    #[test]
    fn rejects_unguarded_bvudiv_dividend() {
        let script = parse_script(
            r"
            (set-logic BV)
            (declare-fun a () (_ BitVec 8))
            (declare-fun b () (_ BitVec 8))
            (assert (forall ((x (_ BitVec 8))) (= (bvudiv x a) b)))
            (check-sat)
        ",
        )
        .unwrap();
        assert!(bv_forall_nonconstant_refutation(&script.arena, &script.assertions).is_none());
    }
}
