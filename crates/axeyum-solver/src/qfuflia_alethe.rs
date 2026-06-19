//! Zero-trust-hole Alethe proof **emission** for `QF_UFLIA` / `QF_UFLRA`
//! refutations decided via the **Ackermann reduction over arithmetic** —
//! the arithmetic twin of [`crate::prove_qf_ufbv_unsat_alethe`].
//!
//! The conflict this closes is **congruence then arithmetic**. For
//! `f(x) = 1 ∧ f(y) = 2 ∧ x = y` (with `f : Int → Int`, and the `Real`
//! analogue) the refutation is:
//!
//! 1. one **congruence** step — `x = y ⊢ f(x) = f(y)`, i.e. `v0 = v1` for the
//!    Ackermann abstractions `v0 = f(x)`, `v1 = f(y)`; and
//! 2. a pure **linear-arithmetic** contradiction —
//!    `v0 = 1 ∧ v1 = 2 ∧ v0 = v1 ⊢ 1 = 2`.
//!
//! Both halves are checkable Alethe rules (`eq_congruent`/`eq_transitive`/`symm`
//! for the congruence, `lia_generic`/`la_generic` for the arithmetic), so the
//! whole composes to a **zero-trust** certificate: the otherwise-trusted
//! functional-consistency reduction is *derived*, and the arithmetic
//! contradiction is re-checked by the arithmetic-aware kernel.
//!
//! ## The composed proof
//!
//! [`prove_qf_uflia_unsat_alethe`] reuses the
//! [`crate::qfufbv_alethe::AckermannCongruence`] prefix (shared verbatim with the
//! bit-vector path — every UF application abstracted to a fresh **same-sorted**
//! constant, the derivable consistency consequents `(= v_i v_j)` collected) and
//! then, instead of bit-blasting the reduced problem, hands the reduced
//! (Ackermannized) **pure-arithmetic** conjunction to
//! [`crate::prove_lia_unsat_alethe`] / [`crate::prove_lra_unsat_alethe`]. That
//! emitter `assume`s each reduced atom — including each consequent `(= v_i v_j)` —
//! and refutes them with one `lia_generic`/`la_generic` clause. The
//! [`crate::qfufbv_alethe::AckermannCongruence::splice`] step then replaces each
//! consequent's `Assume` with its `eq_congruent` derivation under the same id, so
//! the consistency constraint is proven from the argument equality and the
//! abstraction's defining equations rather than assumed.
//!
//! Emission is **self-validating**: the assembled mixed proof (congruence steps +
//! arithmetic clause) is run through [`crate::check_alethe_lra`] — which checks
//! both the base Alethe rules *and* the `lia_generic`/`la_generic` clause — before
//! return, so a returned certificate is always re-checkable end-to-end.

use axeyum_cnf::AletheCommand;
use axeyum_ir::{Sort, TermArena, TermId, TermNode};

use crate::qfufbv_alethe::build_ackermann_congruence;

/// Emits a complete, [`crate::check_alethe_lra`]-checkable Alethe refutation for an
/// `unsat` `QF_UFLIA` / `QF_UFLRA` conjunction decided by the Ackermann reduction
/// — with every functional-consistency constraint **proven** by `eq_congruent`
/// (the congruence half) and the residual linear-arithmetic contradiction proven
/// by `lia_generic`/`la_generic` (the arithmetic half) — or [`None`] when the
/// query is outside the fragment.
///
/// The whole certificate has **no trusted reduction step**: the congruence is
/// re-derived, the arithmetic is re-derived, and the assembled proof is accepted
/// by [`crate::check_alethe_lra`] before return.
///
/// Returns [`None`] when:
///
/// - the conjunction contains no uninterpreted-function applications (a pure-LIA/
///   LRA `unsat` is handled directly by [`crate::prove_lia_unsat_alethe`] /
///   [`crate::prove_lra_unsat_alethe`]);
/// - any uninterpreted-function application is **not** arithmetic-sorted (`Int` or
///   `Real`) — the bit-vector path ([`crate::prove_qf_ufbv_unsat_alethe`]) owns
///   the `BitVec` fragment, and arrays/datatypes/quantifiers are out of scope;
/// - no consistency consequent is derivable, or the reduced (Ackermannized)
///   conjunction is not a genuine `unsat` the arithmetic emitter can refute (e.g.
///   a nonlinear residual); or
/// - the assembled proof fails its own [`crate::check_alethe_lra`] re-check.
///
/// Requires `&mut TermArena` because the Ackermann reduction interns fresh
/// abstraction symbols and the consequent equalities `(= v_i v_j)`.
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_uflia_unsat_alethe(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Restrict to arithmetic-sorted UF: every uninterpreted application must be
    // `Int`- or `Real`-sorted, so the Ackermannized residual is pure LIA/LRA. A
    // `BitVec`-sorted application belongs to the bit-vector path; an array/
    // datatype/quantifier query is out of scope. (Mixed BV+arith UF is declined
    // here and handled, if at all, by the bit-vector route.)
    if !all_uf_applications_arithmetic(arena, assertions) {
        return None;
    }

    let congruence = build_ackermann_congruence(arena, assertions)?;

    // The reduced (Ackermannized) problem: rewritten originals plus the
    // consistency *consequents* `(= v_i v_j)`. With every UF application
    // arithmetic-sorted, this is a pure linear-integer/real conjunction.
    let reduced = congruence.reduced_assertions();

    // Refute the residual with the arithmetic emitter: the integer (LIA) route
    // first, then the real (LRA) route. Each `assume`s every reduced atom —
    // including each consequent `(= v_i v_j)` — and refutes them with one
    // `lia_generic`/`la_generic` clause.
    let residual_proof = crate::prove_lia_unsat_alethe(arena, &reduced)
        .or_else(|| crate::prove_lra_unsat_alethe(arena, &reduced))?;

    // Splice: replace each consequent's `Assume` with its `eq_congruent`
    // derivation under the same id, so the consistency constraint is proven. The
    // rest of the arithmetic proof (the other assumes, the `lia_generic`/
    // `la_generic` clause, the closing resolution) is left intact.
    let spliced = congruence.splice(arena, &residual_proof)?;

    // Self-validate with the arithmetic-aware checker (it re-checks BOTH the base
    // Alethe congruence rules AND the `lia_generic`/`la_generic` clause). Return
    // the proof only on a clean re-check — never an unverifiable certificate.
    if matches!(crate::check_alethe_lra(&spliced), Ok(true)) {
        Some(spliced)
    } else {
        None
    }
}

/// Whether **every** uninterpreted-function application in `assertions` is
/// arithmetic-sorted (`Int` or `Real`). Returns `true` for a query with no UF
/// applications too (the caller's `build_ackermann_congruence` then declines), so
/// the gate is purely "no non-arith-sorted UF application is present". A `false`
/// result means a `BitVec` (or other) sorted application exists, so the
/// arithmetic residual would not be pure LIA/LRA and the cert is declined.
fn all_uf_applications_arithmetic(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, axeyum_ir::Op::Apply(_))
                && !matches!(arena.sort_of(term), Sort::Int | Sort::Real)
            {
                return false;
            }
            stack.extend(args.iter().copied());
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::prove_qf_uflia_unsat_alethe;
    use crate::check_alethe_lra;
    use axeyum_ir::{Sort, TermArena};

    /// `f(x) = 1 ∧ f(y) = 2 ∧ x = y` over `f : Int → Int` is UNSAT, and the
    /// assembled congruence-then-arithmetic proof re-checks end-to-end.
    #[test]
    fn emits_checkable_uflia_refutation() {
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let fy = arena.apply(f, &[y]).unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let a1 = arena.eq(fx, one).unwrap();
        let a2 = arena.eq(fy, two).unwrap();
        let a3 = arena.eq(x, y).unwrap();

        let proof = prove_qf_uflia_unsat_alethe(&mut arena, &[a1, a2, a3])
            .expect("emits a QF_UFLIA refutation");
        assert_eq!(check_alethe_lra(&proof), Ok(true));
    }

    /// The `Real` twin: `f(x) = 1 ∧ f(y) = 2 ∧ x = y` over `f : Real → Real`.
    #[test]
    fn emits_checkable_uflra_refutation() {
        use axeyum_ir::Rational;
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let fy = arena.apply(f, &[y]).unwrap();
        let one = arena.real_const(Rational::integer(1));
        let two = arena.real_const(Rational::integer(2));
        let a1 = arena.eq(fx, one).unwrap();
        let a2 = arena.eq(fy, two).unwrap();
        let a3 = arena.eq(x, y).unwrap();

        let proof = prove_qf_uflia_unsat_alethe(&mut arena, &[a1, a2, a3])
            .expect("emits a QF_UFLRA refutation");
        assert_eq!(check_alethe_lra(&proof), Ok(true));
    }

    /// A 2-ary UF: `f(a, b) = 1 ∧ f(c, d) = 2 ∧ a = c ∧ b = d` is UNSAT by
    /// congruence on both arguments then arithmetic.
    #[test]
    fn emits_checkable_two_arg_uflia_refutation() {
        let mut arena = TermArena::new();
        let func = arena
            .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
            .unwrap();
        let a1 = arena.int_var("a1").unwrap();
        let b1 = arena.int_var("b1").unwrap();
        let a2 = arena.int_var("a2").unwrap();
        let b2 = arena.int_var("b2").unwrap();
        let fab = arena.apply(func, &[a1, b1]).unwrap();
        let fcd = arena.apply(func, &[a2, b2]).unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let e1 = arena.eq(fab, one).unwrap();
        let e2 = arena.eq(fcd, two).unwrap();
        let e3 = arena.eq(a1, a2).unwrap();
        let e4 = arena.eq(b1, b2).unwrap();

        let proof = prove_qf_uflia_unsat_alethe(&mut arena, &[e1, e2, e3, e4])
            .expect("emits a 2-ary QF_UFLIA refutation");
        assert_eq!(check_alethe_lra(&proof), Ok(true));
    }

    /// No UF applications → declined (the pure-LIA path owns it).
    #[test]
    fn declines_pure_lia() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let a1 = arena.int_le(x, zero).unwrap();
        let a2 = arena.int_ge(x, one).unwrap();
        assert!(prove_qf_uflia_unsat_alethe(&mut arena, &[a1, a2]).is_none());
    }

    /// A satisfiable UF+arith query → no refutation.
    #[test]
    fn declines_satisfiable_uflia() {
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let fy = arena.apply(f, &[y]).unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        // f(x)=1 ∧ f(y)=2 with x ≠ y (no congruence collapse) is SAT.
        let a1 = arena.eq(fx, one).unwrap();
        let a2 = arena.eq(fy, two).unwrap();
        assert!(prove_qf_uflia_unsat_alethe(&mut arena, &[a1, a2]).is_none());
    }
}
