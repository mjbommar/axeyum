//! Finite-domain array refuters.
//!
//! This covers the small, explicit `QF_ABV`/`QF_AUFBV` shape where two arrays over
//! a finite BV index sort are asserted unequal while every concrete read in that
//! finite domain is asserted equal, plus the analogous Bool-index read-collapse
//! shape where the two concrete reads of one array are asserted equal but two
//! arbitrary reads of that array are asserted unequal.

use std::collections::BTreeMap;

use axeyum_ir::{ArraySortKey, Op, Sort, TermArena, TermId, TermNode};

/// Keep the first certificate slice small enough to be readable in Lean and cheap
/// in dominance audits.
pub const MAX_FINITE_ARRAY_EXT_READS: u128 = 16;

/// One asserted pointwise read equality used by a finite-array extensionality
/// refutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FiniteArrayReadEquality {
    /// The original top-level equality term.
    pub equality: TermId,
    /// The left read term, matching the certificate's `lhs_array`.
    pub lhs_read: TermId,
    /// The right read term, matching the certificate's `rhs_array`.
    pub rhs_read: TermId,
    /// Concrete BV index value of both reads.
    pub index_value: u128,
}

/// A self-checking finite-array extensionality refutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FiniteArrayExtensionalityCertificate {
    /// Left array from the asserted disequality.
    pub lhs_array: TermId,
    /// Right array from the asserted disequality.
    pub rhs_array: TermId,
    /// BV width of the finite index domain.
    pub index_width: u32,
    /// One read equality for each concrete index value, in ascending value order.
    pub read_equalities: Vec<FiniteArrayReadEquality>,
}

/// A self-checking Bool-index array read-collapse refutation.
///
/// For an array `a : Array Bool E`, the assertion
/// `select a false = select a true` makes all reads from `a` equal, because every
/// Boolean index is either `false` or `true`. A simultaneous disequality between
/// two reads of `a` is therefore impossible.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolArrayReadCollapseCertificate {
    /// The array whose Bool-index domain has collapsed to one read value.
    pub array: TermId,
    /// The original top-level equality between the concrete `false` and `true`
    /// reads.
    pub concrete_equality: TermId,
    /// The read at index `false`, oriented from `concrete_equality`.
    pub false_read: TermId,
    /// The read at index `true`, oriented from `concrete_equality`.
    pub true_read: TermId,
    /// The original top-level disequality between two arbitrary reads of
    /// `array`.
    pub disequality: TermId,
    /// Left read from `disequality`.
    pub lhs_read: TermId,
    /// Right read from `disequality`.
    pub rhs_read: TermId,
}

impl BoolArrayReadCollapseCertificate {
    /// Re-runs the deterministic matcher against the original assertions.
    #[must_use]
    pub fn recheck(&self, arena: &TermArena, assertions: &[TermId]) -> bool {
        bool_array_read_collapse_refutation(arena, assertions).is_some_and(|fresh| fresh == *self)
    }
}

/// Returns a finite-array extensionality certificate when the top-level
/// conjunction contains:
///
/// - `not (= a b)`, where `a` and `b` have the same array sort with BV index;
/// - for every concrete index value `i`, `(= (select a i) (select b i))`.
#[must_use]
pub fn finite_array_extensionality_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<FiniteArrayExtensionalityCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    let mut read_equalities: BTreeMap<(TermId, TermId, u128), FiniteArrayReadEquality> =
        BTreeMap::new();
    let mut disequalities = Vec::new();
    for &conjunct in &conjuncts {
        if let Some(read_eq) = match_read_equality(arena, conjunct) {
            read_equalities.insert(
                (read_eq.lhs_array, read_eq.rhs_array, read_eq.index_value),
                FiniteArrayReadEquality {
                    equality: conjunct,
                    lhs_read: read_eq.lhs_read,
                    rhs_read: read_eq.rhs_read,
                    index_value: read_eq.index_value,
                },
            );
        }
        if let Some(diseq) = match_array_disequality(arena, conjunct) {
            disequalities.push(diseq);
        }
    }

    for diseq in disequalities {
        let Some(domain_size) = finite_bv_domain_size(diseq.index_width) else {
            continue;
        };
        let mut reads = Vec::with_capacity(domain_size as usize);
        let mut complete = true;
        for value in 0..domain_size {
            if let Some(read_eq) = read_equalities.get(&(diseq.lhs_array, diseq.rhs_array, value)) {
                reads.push(read_eq.clone());
            } else {
                complete = false;
                break;
            }
        }
        if !complete {
            continue;
        }
        return Some(FiniteArrayExtensionalityCertificate {
            lhs_array: diseq.lhs_array,
            rhs_array: diseq.rhs_array,
            index_width: diseq.index_width,
            read_equalities: reads,
        });
    }
    None
}

/// Returns a Bool-index array read-collapse certificate when the top-level
/// conjunction contains:
///
/// - `(= (select a false) (select a true))`, in either orientation; and
/// - `(not (= (select a i) (select a j)))`, where `i` and `j` are Bool-sorted
///   terms.
#[must_use]
pub fn bool_array_read_collapse_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BoolArrayReadCollapseCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    let mut concrete_equalities: BTreeMap<TermId, BoolConcreteReadEquality> = BTreeMap::new();
    let mut disequalities = Vec::new();
    for &conjunct in &conjuncts {
        if let Some(eq) = match_bool_concrete_read_equality(arena, conjunct) {
            concrete_equalities.entry(eq.array).or_insert(eq);
        }
        if let Some(diseq) = match_bool_read_disequality(arena, conjunct) {
            disequalities.push(diseq);
        }
    }

    for diseq in disequalities {
        let Some(eq) = concrete_equalities.get(&diseq.array) else {
            continue;
        };
        return Some(BoolArrayReadCollapseCertificate {
            array: diseq.array,
            concrete_equality: eq.equality,
            false_read: eq.false_read,
            true_read: eq.true_read,
            disequality: diseq.disequality,
            lhs_read: diseq.lhs_read,
            rhs_read: diseq.rhs_read,
        });
    }
    None
}

#[derive(Debug, Clone, Copy)]
struct ArrayDisequality {
    lhs_array: TermId,
    rhs_array: TermId,
    index_width: u32,
}

#[derive(Debug, Clone, Copy)]
struct ReadEquality {
    lhs_array: TermId,
    rhs_array: TermId,
    lhs_read: TermId,
    rhs_read: TermId,
    index_value: u128,
}

#[derive(Debug, Clone, Copy)]
struct BoolConcreteReadEquality {
    equality: TermId,
    array: TermId,
    false_read: TermId,
    true_read: TermId,
}

#[derive(Debug, Clone, Copy)]
struct BoolReadDisequality {
    disequality: TermId,
    array: TermId,
    lhs_read: TermId,
    rhs_read: TermId,
}

fn finite_bv_domain_size(width: u32) -> Option<u128> {
    let size = 1_u128.checked_shl(width)?;
    if size <= MAX_FINITE_ARRAY_EXT_READS {
        Some(size)
    } else {
        None
    }
}

fn collect_top_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 => {
            collect_top_conjuncts(arena, args[0], out);
            collect_top_conjuncts(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn match_array_disequality(arena: &TermArena, term: TermId) -> Option<ArrayDisequality> {
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
    let lhs_sort = arena.sort_of(*lhs);
    if lhs_sort != arena.sort_of(*rhs) {
        return None;
    }
    let Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        ..
    } = lhs_sort
    else {
        return None;
    };
    finite_bv_domain_size(index_width)?;
    Some(ArrayDisequality {
        lhs_array: *lhs,
        rhs_array: *rhs,
        index_width,
    })
}

fn match_read_equality(arena: &TermArena, term: TermId) -> Option<ReadEquality> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    let lhs_read = match_const_select(arena, *lhs)?;
    let rhs_read = match_const_select(arena, *rhs)?;
    if lhs_read.index_width != rhs_read.index_width
        || lhs_read.index_value != rhs_read.index_value
        || arena.sort_of(lhs_read.array) != arena.sort_of(rhs_read.array)
        || arena.sort_of(*lhs) != arena.sort_of(*rhs)
    {
        return None;
    }
    Some(ReadEquality {
        lhs_array: lhs_read.array,
        rhs_array: rhs_read.array,
        lhs_read: *lhs,
        rhs_read: *rhs,
        index_value: lhs_read.index_value,
    })
}

fn match_bool_concrete_read_equality(
    arena: &TermArena,
    term: TermId,
) -> Option<BoolConcreteReadEquality> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    let lhs_read = match_bool_select(arena, *lhs)?;
    let rhs_read = match_bool_select(arena, *rhs)?;
    if lhs_read.array != rhs_read.array || arena.sort_of(*lhs) != arena.sort_of(*rhs) {
        return None;
    }
    let lhs_index = bool_const_value(arena, lhs_read.index)?;
    let rhs_index = bool_const_value(arena, rhs_read.index)?;
    if lhs_index == rhs_index {
        return None;
    }
    let (false_read, true_read) = if !lhs_index && rhs_index {
        (*lhs, *rhs)
    } else {
        (*rhs, *lhs)
    };
    Some(BoolConcreteReadEquality {
        equality: term,
        array: lhs_read.array,
        false_read,
        true_read,
    })
}

fn match_bool_read_disequality(arena: &TermArena, term: TermId) -> Option<BoolReadDisequality> {
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
    if lhs == rhs {
        return None;
    }
    let lhs_read = match_bool_select(arena, *lhs)?;
    let rhs_read = match_bool_select(arena, *rhs)?;
    if lhs_read.array != rhs_read.array || arena.sort_of(*lhs) != arena.sort_of(*rhs) {
        return None;
    }
    Some(BoolReadDisequality {
        disequality: term,
        array: lhs_read.array,
        lhs_read: *lhs,
        rhs_read: *rhs,
    })
}

#[derive(Debug, Clone, Copy)]
struct BoolSelect {
    array: TermId,
    index: TermId,
}

fn match_bool_select(arena: &TermArena, term: TermId) -> Option<BoolSelect> {
    let TermNode::App {
        op: Op::Select,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [array, index] = &**args else {
        return None;
    };
    if arena.sort_of(*index) != Sort::Bool {
        return None;
    }
    let Sort::Array {
        index: ArraySortKey::Bool,
        ..
    } = arena.sort_of(*array)
    else {
        return None;
    };
    Some(BoolSelect {
        array: *array,
        index: *index,
    })
}

fn bool_const_value(arena: &TermArena, term: TermId) -> Option<bool> {
    let TermNode::BoolConst(value) = arena.node(term) else {
        return None;
    };
    Some(*value)
}

#[derive(Debug, Clone, Copy)]
struct ConstSelect {
    array: TermId,
    index_width: u32,
    index_value: u128,
}

fn match_const_select(arena: &TermArena, term: TermId) -> Option<ConstSelect> {
    let TermNode::App {
        op: Op::Select,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [array, index] = &**args else {
        return None;
    };
    let TermNode::BvConst { width, value } = arena.node(*index) else {
        return None;
    };
    let Sort::Array {
        index: ArraySortKey::BitVec(array_index_width),
        ..
    } = arena.sort_of(*array)
    else {
        return None;
    };
    if *width != array_index_width {
        return None;
    }
    finite_bv_domain_size(*width)?;
    Some(ConstSelect {
        array: *array,
        index_width: *width,
        index_value: *value,
    })
}

#[cfg(test)]
mod tests {
    use axeyum_ir::TermArena;

    use super::*;

    #[test]
    fn refutes_two_arrays_equal_at_all_one_bit_indices_and_disequal() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 1, 1).unwrap();
        let b = arena.array_var("b", 1, 1).unwrap();
        let i0 = arena.bv_const(1, 0).unwrap();
        let i1 = arena.bv_const(1, 1).unwrap();
        let a0 = arena.select(a, i0).unwrap();
        let b0 = arena.select(b, i0).unwrap();
        let a1 = arena.select(a, i1).unwrap();
        let b1 = arena.select(b, i1).unwrap();
        let e0 = arena.eq(a0, b0).unwrap();
        let e1 = arena.eq(a1, b1).unwrap();
        let ne = {
            let eq = arena.eq(a, b).unwrap();
            arena.not(eq).unwrap()
        };

        let cert = finite_array_extensionality_refutation(&arena, &[e0, e1, ne])
            .expect("pointwise equality over the finite index domain refutes disequality");
        assert_eq!(cert.lhs_array, a);
        assert_eq!(cert.rhs_array, b);
        assert_eq!(cert.index_width, 1);
        assert_eq!(
            cert.read_equalities
                .iter()
                .map(|read| read.index_value)
                .collect::<Vec<_>>(),
            vec![0, 1]
        );
    }

    #[test]
    fn declines_when_one_finite_index_is_missing() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 2, 2).unwrap();
        let b = arena.array_var("b", 2, 2).unwrap();
        let mut assertions = Vec::new();
        for value in 0..3 {
            let idx = arena.bv_const(2, value).unwrap();
            let lhs = arena.select(a, idx).unwrap();
            let rhs = arena.select(b, idx).unwrap();
            assertions.push(arena.eq(lhs, rhs).unwrap());
        }
        let ne = {
            let eq = arena.eq(a, b).unwrap();
            arena.not(eq).unwrap()
        };
        assertions.push(ne);

        assert!(finite_array_extensionality_refutation(&arena, &assertions).is_none());
    }

    #[test]
    fn refutes_bool_index_read_collapse_disequality() {
        let mut arena = TermArena::new();
        let a = arena
            .array_var_with_sorts("a", Sort::Bool, Sort::Bool)
            .unwrap();
        let p = {
            let sym = arena.declare("p", Sort::Bool).unwrap();
            arena.var(sym)
        };
        let not_p = arena.not(p).unwrap();
        let false_term = arena.bool_const(false);
        let true_term = arena.bool_const(true);
        let a_false = arena.select(a, false_term).unwrap();
        let a_true = arena.select(a, true_term).unwrap();
        let concrete_eq = arena.eq(a_false, a_true).unwrap();
        let a_p = arena.select(a, p).unwrap();
        let a_not_p = arena.select(a, not_p).unwrap();
        let read_eq = arena.eq(a_p, a_not_p).unwrap();
        let read_ne = arena.not(read_eq).unwrap();

        let cert = bool_array_read_collapse_refutation(&arena, &[read_ne, concrete_eq])
            .expect("Bool-index concrete read equality refutes arbitrary read disequality");
        assert_eq!(cert.array, a);
        assert_eq!(cert.concrete_equality, concrete_eq);
        assert_eq!(cert.false_read, a_false);
        assert_eq!(cert.true_read, a_true);
        assert_eq!(cert.disequality, read_ne);
        assert!(cert.recheck(&arena, &[read_ne, concrete_eq]));
    }

    #[test]
    fn bool_index_read_collapse_needs_same_array() {
        let mut arena = TermArena::new();
        let a = arena
            .array_var_with_sorts("a", Sort::Bool, Sort::Bool)
            .unwrap();
        let b = arena
            .array_var_with_sorts("b", Sort::Bool, Sort::Bool)
            .unwrap();
        let p = {
            let sym = arena.declare("p", Sort::Bool).unwrap();
            arena.var(sym)
        };
        let false_term = arena.bool_const(false);
        let true_term = arena.bool_const(true);
        let a_false = arena.select(a, false_term).unwrap();
        let a_true = arena.select(a, true_term).unwrap();
        let concrete_eq = arena.eq(a_false, a_true).unwrap();
        let a_p = arena.select(a, p).unwrap();
        let b_p = arena.select(b, p).unwrap();
        let read_eq = arena.eq(a_p, b_p).unwrap();
        let read_ne = arena.not(read_eq).unwrap();

        assert!(bool_array_read_collapse_refutation(&arena, &[read_ne, concrete_eq]).is_none());
    }
}
