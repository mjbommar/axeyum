//! Small checked even-power refutations for NRA.
//!
//! This module recognizes strict-real inequalities whose left side is a sum of
//! syntactic even powers of real terms plus a nonnegative rational constant, and
//! whose right side is zero. Such a left side is nonnegative over the reals, so
//! asserting it is `< 0` is impossible. The matcher is deliberately narrow and
//! re-checkable: callers use the certificate only after re-scanning the original
//! assertions.

use axeyum_ir::{Op, Rational, TermArena, TermId, TermNode};

/// A self-checking refutation of a strict negative even-power sum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NraEvenPowerRefutationCertificate {
    /// The original top-level conjunct refuted by the certificate.
    pub assertion: TermId,
    /// Number of syntactic even-power summands found in the nonnegative sum.
    pub even_power_terms: u32,
    /// The largest accepted even exponent.
    pub max_even_exponent: u32,
    /// The nonnegative rational constant folded out of the sum.
    pub constant: Rational,
}

#[derive(Debug, Clone, Copy)]
struct NonnegativeSum {
    even_power_terms: u32,
    max_even_exponent: u32,
    constant: Rational,
}

/// Returns a certificate when any top-level conjunct has the checked shape
/// `nonnegative_even_power_sum < 0`.
#[must_use]
pub fn nra_even_power_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<NraEvenPowerRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    conjuncts.into_iter().find_map(|assertion| {
        let sum = match_even_power_lt_zero(arena, assertion)?;
        Some(NraEvenPowerRefutationCertificate {
            assertion,
            even_power_terms: sum.even_power_terms,
            max_even_exponent: sum.max_even_exponent,
            constant: sum.constant,
        })
    })
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

fn match_even_power_lt_zero(arena: &TermArena, assertion: TermId) -> Option<NonnegativeSum> {
    let TermNode::App {
        op: Op::RealLt,
        args,
    } = arena.node(assertion)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if !is_real_zero(arena, *rhs) {
        return None;
    }
    nonnegative_even_power_sum(arena, *lhs)
}

fn nonnegative_even_power_sum(arena: &TermArena, term: TermId) -> Option<NonnegativeSum> {
    let mut summands = Vec::new();
    flatten_real_add(arena, term, &mut summands);
    if summands.is_empty() {
        return None;
    }

    let mut even_power_terms = 0_u32;
    let mut max_even_exponent = 0_u32;
    let mut constant = Rational::zero();
    for summand in summands {
        if let TermNode::RealConst(value) = arena.node(summand) {
            if value.numerator() < 0 {
                return None;
            }
            constant = constant.checked_add(*value)?;
            continue;
        }

        let exponent = even_power_exponent(arena, summand)?;
        even_power_terms = even_power_terms.checked_add(1)?;
        max_even_exponent = max_even_exponent.max(exponent);
    }

    Some(NonnegativeSum {
        even_power_terms,
        max_even_exponent,
        constant,
    })
}

fn flatten_real_add(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::RealAdd,
            args,
        } if args.len() >= 2 => {
            for &arg in args {
                flatten_real_add(arena, arg, out);
            }
        }
        _ => out.push(term),
    }
}

fn even_power_exponent(arena: &TermArena, term: TermId) -> Option<u32> {
    let mut factors = Vec::new();
    flatten_real_mul(arena, term, &mut factors);
    if factors.len() < 2 || factors.len() % 2 != 0 {
        return None;
    }
    let first = *factors.first()?;
    if arena.sort_of(first) != axeyum_ir::Sort::Real {
        return None;
    }
    if factors.iter().any(|&factor| factor != first) {
        return None;
    }
    u32::try_from(factors.len()).ok()
}

fn flatten_real_mul(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::RealMul,
            args,
        } if args.len() >= 2 => {
            for &arg in args {
                flatten_real_mul(arena, arg, out);
            }
        }
        _ => out.push(term),
    }
}

fn is_real_zero(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), TermNode::RealConst(value) if value.is_zero())
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Rational, TermArena};

    use super::nra_even_power_refutation;

    #[test]
    fn recognizes_fourth_power_negative() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let x2 = arena.real_mul(x, x).unwrap();
        let x4 = arena.real_mul(x2, x2).unwrap();
        let zero = arena.real_const(Rational::zero());
        let assertion = arena.real_lt(x4, zero).unwrap();

        let cert = nra_even_power_refutation(&arena, &[assertion]).unwrap();
        assert_eq!(cert.assertion, assertion);
        assert_eq!(cert.even_power_terms, 1);
        assert_eq!(cert.max_even_exponent, 4);
        assert_eq!(cert.constant, Rational::zero());
    }

    #[test]
    fn recognizes_shifted_fourth_power_sum_plus_one() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let one = arena.real_const(Rational::integer(1));
        let two = arena.real_const(Rational::integer(2));
        let zero = arena.real_const(Rational::zero());
        let xm1 = arena.real_sub(x, one).unwrap();
        let ym2 = arena.real_sub(y, two).unwrap();
        let xm1_2 = arena.real_mul(xm1, xm1).unwrap();
        let ym2_2 = arena.real_mul(ym2, ym2).unwrap();
        let xm1_4 = arena.real_mul(xm1_2, xm1_2).unwrap();
        let ym2_4 = arena.real_mul(ym2_2, ym2_2).unwrap();
        let sum = arena.real_add(xm1_4, ym2_4).unwrap();
        let lhs = arena.real_add(sum, one).unwrap();
        let assertion = arena.real_lt(lhs, zero).unwrap();

        let cert = nra_even_power_refutation(&arena, &[assertion]).unwrap();
        assert_eq!(cert.even_power_terms, 2);
        assert_eq!(cert.max_even_exponent, 4);
        assert_eq!(cert.constant, Rational::integer(1));
    }

    #[test]
    fn rejects_odd_power_negative() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let x2 = arena.real_mul(x, x).unwrap();
        let x3 = arena.real_mul(x2, x).unwrap();
        let zero = arena.real_const(Rational::zero());
        let assertion = arena.real_lt(x3, zero).unwrap();

        assert!(nra_even_power_refutation(&arena, &[assertion]).is_none());
    }
}
