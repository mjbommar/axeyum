//! Finite-domain cardinality refuters for `QF_UFBV`.
//!
//! The pure EUF fast path deliberately treats base sorts abstractly, while the
//! BV backend can only bit-blast bit-vector carriers. This small bridge covers a
//! common mixed case: too many pairwise-distinct applications of the same
//! function over a finite BV/Bool argument domain.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{FuncId, Op, Sort, SymbolId, TermArena, TermId, TermNode};

const BOOL_UF_EXHAUSTIVE_MAX_BITS: usize = 12;

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

/// A self-checking exhaustive refutation for small Boolean-UF formulas.
///
/// The checker enumerates every assignment to the reachable Boolean symbols and
/// every truth table for the reachable uninterpreted functions whose signature is
/// `Bool^n -> Bool`. It accepts only when no assignment/interpretation satisfies
/// all original assertions. This is intentionally narrow: it is a zero-reduction
/// certificate for tiny Boolean functional-graph rows, not a replacement for the
/// general UF/BV solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolUfExhaustiveCertificate {
    /// Reachable Boolean free symbols, in deterministic declaration order.
    pub bool_symbols: Vec<SymbolId>,
    /// Reachable `Bool^n -> Bool` uninterpreted functions, in declaration order.
    pub functions: Vec<FuncId>,
    /// Number of assignments/interpretations exhaustively evaluated.
    pub cases: u64,
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

/// Returns an exhaustive finite-Boolean-UF certificate for tiny formulas.
#[must_use]
pub fn bool_uf_exhaustive_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BoolUfExhaustiveCertificate> {
    let mut signature = BoolUfSignature::default();
    for &assertion in assertions {
        collect_bool_uf_signature(arena, assertion, &mut signature)?;
    }
    if signature.functions.is_empty() {
        return None;
    }

    let mut bits = signature.symbols.len();
    let mut table_bits = BTreeMap::new();
    for &func in &signature.functions {
        let (_, params, _) = arena.function(func);
        let arity = params.len();
        if arity >= usize::BITS as usize {
            return None;
        }
        let entries = 1_usize.checked_shl(u32::try_from(arity).ok()?)?;
        bits = bits.checked_add(entries)?;
        table_bits.insert(func, entries);
    }
    if bits > BOOL_UF_EXHAUSTIVE_MAX_BITS {
        return None;
    }

    let cases = 1_u64.checked_shl(u32::try_from(bits).ok()?)?;
    for case in 0..cases {
        let interpretation = BoolUfInterpretation::from_case(&signature, &table_bits, case)?;
        let mut all_true = true;
        for &assertion in assertions {
            if !eval_bool_uf_term(arena, assertion, &interpretation)? {
                all_true = false;
                break;
            }
        }
        if all_true {
            return None;
        }
    }

    Some(BoolUfExhaustiveCertificate {
        bool_symbols: signature.symbols.into_iter().collect(),
        functions: signature.functions.into_iter().collect(),
        cases,
    })
}

#[derive(Default)]
struct BoolUfSignature {
    symbols: BTreeSet<SymbolId>,
    functions: BTreeSet<FuncId>,
}

fn collect_bool_uf_signature(
    arena: &TermArena,
    term: TermId,
    signature: &mut BoolUfSignature,
) -> Option<()> {
    match arena.node(term) {
        TermNode::BoolConst(_) => Some(()),
        TermNode::Symbol(symbol) => {
            if arena.symbol(*symbol).1 == Sort::Bool {
                signature.symbols.insert(*symbol);
                Some(())
            } else {
                None
            }
        }
        TermNode::App { op, args } => match op {
            Op::BoolNot if args.len() == 1 => collect_bool_uf_signature(arena, args[0], signature),
            Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies | Op::Eq
                if args.len() == 2 =>
            {
                collect_bool_uf_signature(arena, args[0], signature)?;
                collect_bool_uf_signature(arena, args[1], signature)
            }
            Op::Ite if args.len() == 3 && arena.sort_of(args[1]) == Sort::Bool => {
                collect_bool_uf_signature(arena, args[0], signature)?;
                collect_bool_uf_signature(arena, args[1], signature)?;
                collect_bool_uf_signature(arena, args[2], signature)
            }
            Op::Apply(func) => {
                let (_, params, result) = arena.function(*func);
                if result != Sort::Bool || params.iter().any(|&sort| sort != Sort::Bool) {
                    return None;
                }
                if params.len() != args.len() {
                    return None;
                }
                signature.functions.insert(*func);
                for &arg in &**args {
                    collect_bool_uf_signature(arena, arg, signature)?;
                }
                Some(())
            }
            _ => None,
        },
        TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_) => None,
    }
}

struct BoolUfInterpretation {
    symbol_values: BTreeMap<SymbolId, bool>,
    function_tables: BTreeMap<FuncId, u64>,
}

impl BoolUfInterpretation {
    fn from_case(
        signature: &BoolUfSignature,
        table_bits: &BTreeMap<FuncId, usize>,
        mut case: u64,
    ) -> Option<Self> {
        let mut symbol_values = BTreeMap::new();
        for &symbol in &signature.symbols {
            symbol_values.insert(symbol, (case & 1) != 0);
            case >>= 1;
        }

        let mut function_tables = BTreeMap::new();
        for &func in &signature.functions {
            let bits = *table_bits.get(&func)?;
            let mask = if bits == u64::BITS as usize {
                u64::MAX
            } else {
                (1_u64 << bits) - 1
            };
            function_tables.insert(func, case & mask);
            case >>= bits;
        }
        Some(Self {
            symbol_values,
            function_tables,
        })
    }
}

fn eval_bool_uf_term(
    arena: &TermArena,
    term: TermId,
    interpretation: &BoolUfInterpretation,
) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::Symbol(symbol) => interpretation.symbol_values.get(symbol).copied(),
        TermNode::App { op, args } => match op {
            Op::BoolNot if args.len() == 1 => {
                Some(!eval_bool_uf_term(arena, args[0], interpretation)?)
            }
            Op::BoolAnd if args.len() == 2 => Some(
                eval_bool_uf_term(arena, args[0], interpretation)?
                    && eval_bool_uf_term(arena, args[1], interpretation)?,
            ),
            Op::BoolOr if args.len() == 2 => Some(
                eval_bool_uf_term(arena, args[0], interpretation)?
                    || eval_bool_uf_term(arena, args[1], interpretation)?,
            ),
            Op::BoolXor if args.len() == 2 => Some(
                eval_bool_uf_term(arena, args[0], interpretation)?
                    ^ eval_bool_uf_term(arena, args[1], interpretation)?,
            ),
            Op::BoolImplies if args.len() == 2 => Some(
                !eval_bool_uf_term(arena, args[0], interpretation)?
                    || eval_bool_uf_term(arena, args[1], interpretation)?,
            ),
            Op::Eq if args.len() == 2 => Some(
                eval_bool_uf_term(arena, args[0], interpretation)?
                    == eval_bool_uf_term(arena, args[1], interpretation)?,
            ),
            Op::Ite if args.len() == 3 && arena.sort_of(args[1]) == Sort::Bool => {
                let branch = if eval_bool_uf_term(arena, args[0], interpretation)? {
                    args[1]
                } else {
                    args[2]
                };
                eval_bool_uf_term(arena, branch, interpretation)
            }
            Op::Apply(func) => {
                let table = *interpretation.function_tables.get(func)?;
                let mut index = 0_usize;
                for (bit, &arg) in args.iter().enumerate() {
                    if eval_bool_uf_term(arena, arg, interpretation)? {
                        index |= 1_usize << bit;
                    }
                }
                Some(((table >> index) & 1) != 0)
            }
            _ => None,
        },
        TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_) => None,
    }
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
        | Sort::Uninterpreted(_)
        | Sort::Seq(_) => None,
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
    #![allow(clippy::many_single_char_names, clippy::similar_names)]

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

    #[test]
    fn exhaustively_refutes_boolean_functional_graph() {
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Bool], Sort::Bool).unwrap();
        let a = arena.bool_var("a").unwrap();
        let b = arena.bool_var("b").unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ffb = arena.apply(f, &[fb]).unwrap();
        let fffb = arena.apply(f, &[ffb]).unwrap();
        let a_ne_b = {
            let eq = arena.eq(a, b).unwrap();
            arena.not(eq).unwrap()
        };
        let fa_ne_fb = {
            let eq = arena.eq(fa, fb).unwrap();
            arena.not(eq).unwrap()
        };

        let cert = bool_uf_exhaustive_refutation(&arena, &[a_ne_b, fa_ne_fb, fa, fffb])
            .expect("fun1 Boolean-UF graph is finite-domain unsat");
        assert_eq!(cert.bool_symbols.len(), 2);
        assert_eq!(cert.functions, vec![f]);
        assert_eq!(cert.cases, 16);
    }

    #[test]
    fn exhaustive_bool_uf_declines_satisfiable_functional_graph() {
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Bool], Sort::Bool).unwrap();
        let a = arena.bool_var("a").unwrap();
        let fa = arena.apply(f, &[a]).unwrap();

        assert!(bool_uf_exhaustive_refutation(&arena, &[fa]).is_none());
    }
}
