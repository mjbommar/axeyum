//! Finite-domain cardinality refuters for `QF_UFBV`.
//!
//! The pure EUF fast path deliberately treats base sorts abstractly, while the
//! BV backend can only bit-blast bit-vector carriers. This small bridge covers a
//! common mixed case: too many pairwise-distinct applications of the same
//! function over a finite BV/Bool argument domain.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{FuncId, Op, Sort, TermArena, TermId, TermNode};

/// A self-checking finite-domain pigeonhole refutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FiniteDomainPigeonholeCertificate {
    /// The function whose finite argument domain is over-subscribed.
    pub function: FuncId,
    /// Cardinality of the function's argument tuple domain.
    pub domain_size: u128,
    /// Pairwise-disequal applications of `function`; `len() > domain_size`.
    pub applications: Vec<TermId>,
}

/// Returns a finite-domain pigeonhole certificate when the top-level conjunction
/// requires more distinct outputs of one function than its finite input domain
/// can provide.
#[must_use]
pub fn finite_domain_pigeonhole_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<FiniteDomainPigeonholeCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    let mut by_func: BTreeMap<FuncId, FunctionDiseqs> = BTreeMap::new();
    for conjunct in conjuncts {
        let Some((lhs, rhs)) = match_disequality(arena, conjunct) else {
            continue;
        };
        let Some((lf, _)) = direct_application(arena, lhs) else {
            continue;
        };
        let Some((rf, _)) = direct_application(arena, rhs) else {
            continue;
        };
        if lf != rf {
            continue;
        }
        let entry = by_func.entry(lf).or_default();
        let (a, b) = ordered_pair(lhs, rhs);
        entry.apps.insert(lhs);
        entry.apps.insert(rhs);
        entry.diseqs.insert((a, b));
    }

    for (func, facts) in by_func {
        let (_, params, _) = arena.function(func);
        let domain_size = finite_tuple_cardinality(params)?;
        if facts.apps.len() as u128 <= domain_size {
            continue;
        }
        let apps: Vec<TermId> = facts.apps.into_iter().collect();
        if pairwise_disequal(&apps, &facts.diseqs) {
            return Some(FiniteDomainPigeonholeCertificate {
                function: func,
                domain_size,
                applications: apps,
            });
        }
    }
    None
}

#[derive(Default)]
struct FunctionDiseqs {
    apps: BTreeSet<TermId>,
    diseqs: BTreeSet<(TermId, TermId)>,
}

fn finite_tuple_cardinality(params: &[Sort]) -> Option<u128> {
    let mut product = 1_u128;
    for &param in params {
        product = product.checked_mul(finite_sort_cardinality(param)?)?;
    }
    Some(product)
}

fn finite_sort_cardinality(sort: Sort) -> Option<u128> {
    match sort {
        Sort::Bool => Some(2),
        Sort::BitVec(width) if width < 128 => Some(1_u128 << width),
        Sort::Float { exp, sig } if exp + sig < 128 => Some(1_u128 << (exp + sig)),
        Sort::BitVec(_)
        | Sort::Float { .. }
        | Sort::Int
        | Sort::Real
        | Sort::Array { .. }
        | Sort::Datatype(_)
        | Sort::Uninterpreted(_) => None,
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

fn direct_application(arena: &TermArena, term: TermId) -> Option<(FuncId, &[TermId])> {
    let TermNode::App {
        op: Op::Apply(func),
        args,
    } = arena.node(term)
    else {
        return None;
    };
    Some((*func, args))
}

fn pairwise_disequal(apps: &[TermId], diseqs: &BTreeSet<(TermId, TermId)>) -> bool {
    for (i, &a) in apps.iter().enumerate() {
        for &b in &apps[(i + 1)..] {
            if !diseqs.contains(&ordered_pair(a, b)) {
                return false;
            }
        }
    }
    true
}

fn ordered_pair(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b { (a, b) } else { (b, a) }
}

#[cfg(test)]
mod tests {
    use axeyum_ir::Sort;

    use super::*;

    #[test]
    fn refutes_three_distinct_outputs_from_one_bit_domain() {
        let mut arena = TermArena::new();
        let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("A"));
        let f = arena.declare_fun("f", &[Sort::BitVec(1)], carrier).unwrap();
        let g = arena.declare_fun("g", &[carrier], Sort::BitVec(1)).unwrap();
        let x = arena.declare("x", carrier).unwrap();
        let y = arena.declare("y", carrier).unwrap();
        let z = arena.declare("z", carrier).unwrap();
        let x = arena.var(x);
        let y = arena.var(y);
        let z = arena.var(z);
        let gx = arena.apply(g, &[x]).unwrap();
        let gy = arena.apply(g, &[y]).unwrap();
        let gz = arena.apply(g, &[z]).unwrap();
        let fx = arena.apply(f, &[gx]).unwrap();
        let fy = arena.apply(f, &[gy]).unwrap();
        let fz = arena.apply(f, &[gz]).unwrap();
        let eq_xy = arena.eq(fx, fy).unwrap();
        let eq_xz = arena.eq(fx, fz).unwrap();
        let eq_yz = arena.eq(fy, fz).unwrap();
        let xy = arena.not(eq_xy).unwrap();
        let xz = arena.not(eq_xz).unwrap();
        let yz = arena.not(eq_yz).unwrap();

        let cert = finite_domain_pigeonhole_refutation(&arena, &[xy, xz, yz])
            .expect("three pairwise distinct outputs over a one-bit domain is impossible");
        assert_eq!(cert.function, f);
        assert_eq!(cert.domain_size, 2);
        assert_eq!(cert.applications.len(), 3);
    }

    #[test]
    fn declines_without_pairwise_disequality_clique() {
        let mut arena = TermArena::new();
        let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("A"));
        let f = arena.declare_fun("f", &[Sort::BitVec(1)], carrier).unwrap();
        let a = arena.bv_var("a", 1).unwrap();
        let b = arena.bv_var("b", 1).unwrap();
        let c = arena.bv_var("c", 1).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let fc = arena.apply(f, &[c]).unwrap();
        let eq_ab = arena.eq(fa, fb).unwrap();
        let eq_ac = arena.eq(fa, fc).unwrap();
        let ab = arena.not(eq_ab).unwrap();
        let ac = arena.not(eq_ac).unwrap();

        assert!(finite_domain_pigeonhole_refutation(&arena, &[ab, ac]).is_none());
    }
}
