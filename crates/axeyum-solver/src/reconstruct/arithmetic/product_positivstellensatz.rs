//! Kernel-checked reconstruction of a degree-2 Positivstellensatz refutation.
//!
//! The certificate ([`crate::nra_product_cert`]) says: two asserted hypotheses
//! are lower bounds, and their exact product is the polynomial a third assertion
//! calls negative. This turns that into a Lean term of type `False` that the
//! trusted kernel type-checks over the ordered-ring signature the enclosing
//! [`LraReconstructCtx`] carries — the CONSTRUCTED reals for the shipped route.
//!
//! # The proof
//!
//! With `h₁ : 0 ≤ L`, `h₂ : 0 ≤ R` and `h₃ : L·R < 0`:
//!
//! ```text
//!   nn     := mul_nonneg L R h₁ h₂          : 0 ≤ L·R
//!   absurd := lt_of_le_of_lt 0 (L·R) 0 nn h₃ : 0 < 0
//!   refute := lt_irrefl 0 absurd             : False
//! ```
//!
//! # Strictness is carried, and here it is *weakened* on purpose
//!
//! The certificate distinguishes `> 0` from `≥ 0`, because `p ≥ 0` and `q ≥ 0`
//! give `pq ≥ 0` — refuting `pq < 0` but NOT `pq ≤ 0`. This reconstruction only
//! ever needs the NON-strict direction, so a strict factor is weakened to
//! non-strict via `le_of_lt` before `mul_nonneg`. Weakening a hypothesis is
//! always sound; it is the reverse that would not be.
//!
//! It therefore reconstructs only the `refuted = Negative` case. A `Nonpositive`
//! refuted atom needs `mul_pos` and both factors strict, and is declined rather
//! than approximated — the certificate's own checker already distinguishes them.
//!
//! # Scope: integer coefficients
//!
//! A polynomial becomes a ring expression by building each coefficient from
//! `one` by repeated addition. That is exact and needs no numerals in the
//! signature, but it is linear in the coefficient, so [`MAX_COEFF`] bounds it.
//! Every corpus shape this covers has coefficients in `{±1, ±3}`. A rational or
//! large coefficient declines; clearing denominators is a later slice.

use std::collections::BTreeMap;

use axeyum_lean_kernel::ExprId;

use super::{LraReconstructCtx, ReconstructError};
use crate::nra_product_cert::{AtomSign, NamedPoly, RealProductRefutationCertificate};

/// Largest |coefficient| built by repeated addition of `one`.
///
/// Building `n` costs `n` kernel applications, so this is a real bound and not a
/// style choice. The corpus shapes reconstructed here use `{±1, ±3}`; 64 leaves
/// room without letting a pathological certificate emit a million-node term.
const MAX_COEFF: i128 = 64;

/// `n * one` for an integer `n`, by repeated addition. `None` past [`MAX_COEFF`].
fn integer_expr(ctx: &mut LraReconstructCtx, n: i128) -> Option<ExprId> {
    if n == 0 {
        return Some(ctx.mk_zero());
    }
    let magnitude = n.checked_abs()?;
    if magnitude > MAX_COEFF {
        return None;
    }
    let one = ctx.mk_one();
    let mut acc = one;
    for _ in 1..magnitude {
        acc = ctx.mk_add(acc, one);
    }
    Some(if n < 0 { ctx.mk_neg(acc) } else { acc })
}

/// A polynomial as a ring expression over opaque `R`-typed constants.
///
/// Deterministic: monomials come from a `BTreeMap`, and variable indices are
/// assigned in first-use order over that sorted sequence, so the same
/// certificate always emits the same term.
fn poly_expr(
    ctx: &mut LraReconstructCtx,
    poly: &NamedPoly,
    index_of: &mut BTreeMap<String, usize>,
) -> Option<ExprId> {
    let mut sum: Option<ExprId> = None;
    for (mono, coeff) in poly.terms() {
        if coeff.denominator() != 1 {
            return None; // rational coefficient: a later slice
        }
        let mut term = integer_expr(ctx, coeff.numerator())?;
        for (name, exp) in mono {
            let next = index_of.len();
            let idx = *index_of.entry(name.clone()).or_insert(next);
            let var_name = ctx.var_const(idx);
            let var = ctx.kernel.const_(var_name, vec![]);
            for _ in 0..*exp {
                term = ctx.mk_mul(term, var);
            }
        }
        sum = Some(match sum {
            None => term,
            Some(acc) => ctx.mk_add(acc, term),
        });
    }
    Some(sum.unwrap_or_else(|| ctx.mk_zero()))
}

/// A proof of `0 <= e`, minted at the sign the certificate carries.
///
/// A STRICT factor is asserted as `0 < e` — which is what the query says — and
/// then weakened with `le_of_lt`. Minting `0 <= e` directly would be sound but
/// would put a hypothesis in the module that the query does not state; going
/// through `le_of_lt` keeps the assumed proposition equal to the asserted one
/// and makes the weakening an explicit, kernel-checked step.
fn nonneg_hypothesis(
    ctx: &mut LraReconstructCtx,
    e: ExprId,
    sign: AtomSign,
) -> Result<ExprId, ReconstructError> {
    let zero = ctx.mk_zero();
    match sign {
        AtomSign::Nonnegative => {
            let prop = ctx.mk_le(zero, e);
            ctx.hyp_axiom(prop)
        }
        AtomSign::Positive => {
            let prop = ctx.mk_lt(zero, e);
            let strict = ctx.hyp_axiom(prop)?;
            // `le_of_lt : forall (a b : R), lt a b -> le a b`
            let le_of_lt = ctx.arith().le_of_lt;
            Ok(ctx.apply_const(le_of_lt, &[zero, e, strict]))
        }
        // `Zero` (an equality atom, added for the Handelman route) is a lower
        // bound in principle -- `p = 0` gives `0 <= p` -- but it would need the
        // equality's own transport, and this slice does not build one. Declined
        // rather than approximated.
        AtomSign::Negative | AtomSign::Nonpositive | AtomSign::Zero => {
            Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "a {sign:?} factor is not a usable lower bound for `mul_nonneg` in this slice"
                ),
            })
        }
    }
}

/// Reconstruct the degree-2 Positivstellensatz refutation to `False`.
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] for a `Nonpositive` refuted atom (needs
/// `mul_pos`), a rational or oversized coefficient, or a malformed wire entry;
/// [`ReconstructError::KernelRejected`] if the assembled term does not infer to
/// `False`.
pub(crate) fn reconstruct_real_product(
    ctx: &mut LraReconstructCtx,
    certificate: &RealProductRefutationCertificate,
) -> Result<ExprId, ReconstructError> {
    let (left_sign, right_sign, refuted_sign) = certificate.signs();
    if !matches!(refuted_sign, AtomSign::Negative) {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "product reconstruction closes `L*R < 0` via `mul_nonneg`; a {refuted_sign:?} \
                 refuted atom needs `mul_pos` with both factors strict, which is a later slice"
            ),
        });
    }
    let Some((left_poly, right_poly)) = certificate.factor_polys() else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "certificate carries a malformed factor polynomial".to_owned(),
        });
    };

    let mut index_of: BTreeMap<String, usize> = BTreeMap::new();
    let (Some(left), Some(right)) = (
        poly_expr(ctx, &left_poly, &mut index_of),
        poly_expr(ctx, &right_poly, &mut index_of),
    ) else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "a factor has a rational or |coefficient| > {MAX_COEFF}; building coefficients \
                 from `one` by repeated addition is linear in their size, so this declines \
                 rather than emitting a term proportional to the constant"
            ),
        });
    };

    let zero = ctx.mk_zero();
    let product = ctx.mk_mul(left, right);

    // Hypotheses, minted at the sign the certificate carries. A STRICT factor is
    // weakened to non-strict for `mul_nonneg`; weakening a hypothesis is sound,
    // and this route never needs the strict direction.
    let h_left = nonneg_hypothesis(ctx, left, left_sign)?;
    let h_right = nonneg_hypothesis(ctx, right, right_sign)?;

    // `mul_nonneg : forall (a b : R), le zero a -> le zero b -> le zero (mul a b)`
    let mul_nonneg = ctx.arith().mul_nonneg;
    let nonneg = ctx.apply_const(mul_nonneg, &[left, right, h_left, h_right]);

    // `0 < 0` from `0 <= L*R` and `L*R < 0`, then irreflexivity.
    let lt_product_zero = ctx.mk_lt(product, zero);
    let h_neg = ctx.hyp_axiom(lt_product_zero)?;
    // `lt_of_le_of_lt : forall (a b c : R), le a b -> lt b c -> lt a c`
    let lt_of_le_of_lt = ctx.arith().lt_of_le_of_lt;
    let absurd = ctx.apply_const(lt_of_le_of_lt, &[zero, product, zero, nonneg, h_neg]);
    // `lt_irrefl : forall (a : R), Not (lt a a)`; `Not P` is `P -> False`.
    let lt_irrefl = ctx.arith().lt_irrefl;
    let irrefl = ctx.apply_const(lt_irrefl, &[zero]);
    let proof = ctx.kernel.app(irrefl, absurd);

    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "real_product_positivstellensatz".to_owned(),
            detail: format!("product refutation infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "real_product_positivstellensatz".to_owned(),
            detail: "product refutation did not infer to False".to_owned(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nra_product_cert::real_product_refutation;
    use axeyum_smtlib::parse_script;

    /// `cli__regress1__nl__simple-mono.smt2`: `(x−y) > 0` times `z > 0`.
    const STRICT_FACTORS: &str = "(set-logic QF_NRA)\n\
        (declare-fun x () Real)(declare-fun y () Real)(declare-fun z () Real)\n\
        (assert (> z 0))(assert (> x y))(assert (< (* x z) (* y z)))\n(check-sat)";

    /// `cli__regress1__nl__coeff-unsat-base.smt2`: `(a−3b) >= 0` times `a > 0`.
    /// Exercises a coefficient other than +-1 and a NON-strict factor.
    const MIXED_STRICTNESS: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (> a 0))(assert (> b 0))(assert (>= a (* 3 b)))\n\
        (assert (< (* a a) (* 3 a b)))\n(check-sat)";

    fn certificate(text: &str) -> RealProductRefutationCertificate {
        let p = parse_script(text).expect("parses");
        real_product_refutation(&p.arena, &p.assertions).expect("certificate")
    }

    /// **The measurement that decides whether this is worth having.**
    ///
    /// `LraReconstructCtx::new()` builds `AxReal` — 30 assumptions. The shipped
    /// route's `lra_ctx()` builds `CReal`, trusted surface 0 (ADR-0512). A
    /// refutation checked over the first rests on all 30; this asserts the
    /// second by name, so the module cannot quietly regress onto the axiomatized
    /// package.
    #[test]
    fn both_shapes_kernel_check_over_the_constructed_reals() {
        for text in [STRICT_FACTORS, MIXED_STRICTNESS] {
            let (mut ctx, _) = LraReconstructCtx::try_new_over_constructed_reals_reporting()
                .expect("the constructed real development builds");
            let proof = reconstruct_real_product(&mut ctx, &certificate(text))
                .expect("reconstruction succeeds over CReal");
            let inferred = ctx.kernel_mut().infer(proof).expect("infer");
            let false_ = {
                let f = ctx.arith().logic.false_;
                ctx.kernel_mut().const_(f, vec![])
            };
            assert!(
                ctx.kernel_mut().def_eq(inferred, false_),
                "the term must infer to False over CReal, not only over AxReal"
            );
        }
    }

    #[test]
    fn a_coefficient_past_the_bound_is_declined_not_emitted() {
        // Coefficients are built from `one` by repeated addition, which is
        // linear in their size. A large one must decline rather than emit a term
        // proportional to the constant.
        let mut ctx = LraReconstructCtx::new();
        assert!(integer_expr(&mut ctx, MAX_COEFF).is_some());
        assert!(integer_expr(&mut ctx, -MAX_COEFF).is_some());
        assert!(integer_expr(&mut ctx, MAX_COEFF + 1).is_none());
        assert!(integer_expr(&mut ctx, -(MAX_COEFF + 1)).is_none());
    }

    #[test]
    fn a_nonpositive_refuted_atom_is_declined() {
        // `L*R <= 0` needs `mul_pos` with both factors strict; `mul_nonneg` only
        // refutes `< 0`. Declining is the honest outcome for this slice.
        let text = "(set-logic QF_NRA)\n\
            (declare-fun x () Real)(declare-fun y () Real)\n\
            (assert (> x 0))(assert (> y 0))(assert (<= (* x y) 0))\n(check-sat)";
        let cert = certificate(text);
        let mut ctx = LraReconstructCtx::new();
        let result = reconstruct_real_product(&mut ctx, &cert);
        assert!(
            matches!(result, Err(ReconstructError::UnsupportedTerm { .. })),
            "got {result:?}"
        );
    }
}
