//! GCD divisibility test for linear integer equations (Track 2, P2.4 — the first
//! "cut portfolio" rung).
//!
//! A linear Diophantine equation `Σ aᵢ·xᵢ = b` has an integer solution **iff**
//! `gcd(a₁,…,aₙ)` divides `b`. So a top-level integer equation whose coefficient
//! gcd does not divide its constant is *unsatisfiable* — a sound refutation the
//! rational simplex misses (its LP relaxation is feasible) and that
//! branch-and-bound may not even terminate on when the variables are unbounded
//! (e.g. `2x + 4y = 3`). [`prove_lia_unsat_by_gcd`] checks each top-level equation
//! and reports `unsat` on the first divisibility-infeasible one.
//!
//! **Sound, incomplete:** a positive result is a genuine refutation (a single
//! unsatisfiable conjunct makes the conjunction unsatisfiable); it is silent
//! otherwise (the equation may still be unsatisfiable for other reasons — left to
//! the simplex/branch-and-bound).

use std::collections::BTreeMap;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

/// Tries to prove `assertions` `unsat` by the GCD test on a top-level integer
/// equation. Returns `true` only on a divisibility-infeasible equation (a sound
/// refutation); `false` otherwise.
#[must_use]
pub fn prove_lia_unsat_by_gcd(arena: &TermArena, assertions: &[TermId]) -> bool {
    for &assertion in assertions {
        if let TermNode::App { op: Op::Eq, args } = arena.node(assertion) {
            if args.len() == 2
                && arena.sort_of(args[0]) == Sort::Int
                && equation_is_infeasible(arena, args[0], args[1])
            {
                return true;
            }
        }
    }
    false
}

/// Whether the integer equation `a = b` has no integer solution by the GCD test.
fn equation_is_infeasible(arena: &TermArena, a: TermId, b: TermId) -> bool {
    let (Some((mut coeffs, ka)), Some((cb, kb))) = (int_linear(arena, a), int_linear(arena, b))
    else {
        return false; // non-linear (var·var, div/mod, …): not our test
    };
    // Move `b` to the left: `Σ (ca-cb)·x = -(ka-kb)`.
    for (sym, c) in cb {
        let entry = coeffs.entry(sym).or_insert(0);
        let Some(v) = entry.checked_sub(c) else {
            return false;
        };
        *entry = v;
    }
    let Some(constant) = ka.checked_sub(kb) else {
        return false;
    };
    coeffs.retain(|_, c| *c != 0);

    let mut g: i128 = 0;
    for &c in coeffs.values() {
        g = gcd(g, c);
    }
    if g == 0 {
        // No variables remain: the equation is `constant = 0`, unsat iff non-zero.
        return constant != 0;
    }
    // `Σ coeffs·x = -constant` has an integer solution iff `g | constant`.
    constant % g != 0
}

/// Greatest common divisor of two (possibly negative) integers, as a positive
/// `i128`. `gcd(0, x) = |x|`.
fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    i128::try_from(a).unwrap_or(i128::MAX)
}

/// The linear form of an integer term — a coefficient per symbol plus a constant —
/// or `None` if the term is non-linear (`var·var`, `div`/`mod`, an unsupported
/// operator) or an `i128` overflow occurs.
fn int_linear(arena: &TermArena, t: TermId) -> Option<(BTreeMap<SymbolId, i128>, i128)> {
    match arena.node(t) {
        TermNode::IntConst(n) => Some((BTreeMap::new(), *n)),
        TermNode::Symbol(s) => Some((BTreeMap::from([(*s, 1)]), 0)),
        TermNode::App { op, args } => match (op, &args[..]) {
            (Op::IntNeg, [x]) => scale(int_linear(arena, *x)?, -1),
            (Op::IntAdd, [x, y]) => combine(int_linear(arena, *x)?, int_linear(arena, *y)?, false),
            (Op::IntSub, [x, y]) => combine(int_linear(arena, *x)?, int_linear(arena, *y)?, true),
            (Op::IntMul, [x, y]) => {
                // Linear only if one factor is a (variable-free) constant.
                let (lx, ly) = (int_linear(arena, *x)?, int_linear(arena, *y)?);
                if lx.0.is_empty() {
                    scale(ly, lx.1)
                } else if ly.0.is_empty() {
                    scale(lx, ly.1)
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// `a ± b` over linear forms (`sub` selects subtraction).
fn combine(
    a: (BTreeMap<SymbolId, i128>, i128),
    b: (BTreeMap<SymbolId, i128>, i128),
    sub: bool,
) -> Option<(BTreeMap<SymbolId, i128>, i128)> {
    let (mut coeffs, ka) = a;
    let (cb, kb) = b;
    for (sym, v) in cb {
        let entry = coeffs.entry(sym).or_insert(0);
        *entry = if sub {
            entry.checked_sub(v)?
        } else {
            entry.checked_add(v)?
        };
    }
    let k = if sub {
        ka.checked_sub(kb)?
    } else {
        ka.checked_add(kb)?
    };
    Some((coeffs, k))
}

/// `factor · l` over a linear form.
fn scale(
    l: (BTreeMap<SymbolId, i128>, i128),
    factor: i128,
) -> Option<(BTreeMap<SymbolId, i128>, i128)> {
    let (coeffs, k) = l;
    let mut out = BTreeMap::new();
    for (sym, v) in coeffs {
        out.insert(sym, v.checked_mul(factor)?);
    }
    Some((out, k.checked_mul(factor)?))
}

#[cfg(test)]
mod tests {
    use super::prove_lia_unsat_by_gcd;
    use axeyum_ir::TermArena;

    fn ivar(arena: &mut TermArena, name: &str) -> axeyum_ir::TermId {
        arena.int_var(name).unwrap()
    }

    #[test]
    fn even_combination_equal_to_odd_is_unsat() {
        // 2x + 4y = 3 : gcd(2,4)=2 ∤ 3 ⇒ UNSAT (unbounded — the simplex/B&B miss it).
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let two = arena.int_const(2);
        let four = arena.int_const(4);
        let three = arena.int_const(3);
        let tx = arena.int_mul(two, x).unwrap();
        let fy = arena.int_mul(four, y).unwrap();
        let lhs = arena.int_add(tx, fy).unwrap();
        let eq = arena.eq(lhs, three).unwrap();
        assert!(prove_lia_unsat_by_gcd(&arena, &[eq]));
    }

    #[test]
    fn coprime_combination_is_not_refuted() {
        // 2x + 3y = 1 : gcd(2,3)=1 | 1 ⇒ has a solution, not refuted.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let two = arena.int_const(2);
        let three = arena.int_const(3);
        let one = arena.int_const(1);
        let tx = arena.int_mul(two, x).unwrap();
        let ty = arena.int_mul(three, y).unwrap();
        let lhs = arena.int_add(tx, ty).unwrap();
        let eq = arena.eq(lhs, one).unwrap();
        assert!(!prove_lia_unsat_by_gcd(&arena, &[eq]));
    }

    #[test]
    fn single_coefficient_nondivisor_is_unsat() {
        // 2x = 5 ⇒ UNSAT.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let two = arena.int_const(2);
        let five = arena.int_const(5);
        let tx = arena.int_mul(two, x).unwrap();
        let eq = arena.eq(tx, five).unwrap();
        assert!(prove_lia_unsat_by_gcd(&arena, &[eq]));
    }

    #[test]
    fn inequality_is_not_an_equation() {
        // x ≤ 3 is not an equation — the GCD test does not apply.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let three = arena.int_const(3);
        let le = arena.int_le(x, three).unwrap();
        assert!(!prove_lia_unsat_by_gcd(&arena, &[le]));
    }

    #[test]
    fn rhs_with_variable_is_handled() {
        // 3x = 2y + 1 ⇒ 3x - 2y = 1 : gcd(3,2)=1 | 1 ⇒ has a solution, not refuted.
        // 3x = 3y + 1 ⇒ 3x - 3y = 1 : gcd(3,3)=3 ∤ 1 ⇒ UNSAT.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let three = arena.int_const(3);
        let one = arena.int_const(1);
        let tx = arena.int_mul(three, x).unwrap();
        let ty = arena.int_mul(three, y).unwrap();
        let rhs = arena.int_add(ty, one).unwrap();
        let eq = arena.eq(tx, rhs).unwrap();
        assert!(prove_lia_unsat_by_gcd(&arena, &[eq]));
    }
}
