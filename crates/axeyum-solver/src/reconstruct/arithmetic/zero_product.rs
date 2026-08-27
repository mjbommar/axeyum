//! Kernel-checked reconstruction of a **monomial-divisibility** refutation.
//!
//! The certificate ([`crate::nra_zero_product_cert`]) says: one product is
//! asserted zero, another is asserted non-zero, and every factor of the first is
//! a factor of the second. This module turns that into a Lean term of type
//! `False` that the trusted [`Kernel`] type-checks, over the ordered-ring
//! signature the enclosing [`LraReconstructCtx`] carries — which for the shipped
//! route is the **constructed** reals (`CReal`, trusted surface 0), not the
//! axiomatized package.
//!
//! # The proof
//!
//! Write `M` for the zeroed product and `R` for the remaining factors, so the
//! non-zero product is `M · R`. From `h₁ : M = 0`:
//!
//! ```text
//!   step₁ := congr_mul_left M 0 R h₁   : M · R = 0 · R
//!   step₂ := mul_comm 0 R              : 0 · R = R · 0
//!   step₃ := mul_zero R                : R · 0 = 0
//!   chain := trans (trans step₁ step₂) step₃ : M · R = 0
//!   refute := h₂ chain                 : False        (h₂ : ¬(M · R = 0))
//! ```
//!
//! `zero_mul` is not in the prelude, so the `0 · R = 0` leg goes through
//! `mul_comm` then `mul_zero` — the same detour the Farkas engine already takes
//! at `arithmetic.rs`'s canonicalizer.
//!
//! # What this establishes, and what it does not
//!
//! It is a **theory reconstruction**, not a structural attestation: every step
//! above is a ring law applied to terms built from the certificate's factors, so
//! Lean can reject it on the merits. Compare `ProofFragment::NraEvenPower`,
//! which is classified `StructuralAttestation` — an axiom pair Lean cannot fail.
//!
//! It does **not** by itself bind the hypotheses to the query's `(assert …)`
//! lines. `h₁` and `h₂` are minted here from the certificate, and the binding is
//! the certificate's own two-stage checker
//! ([`crate::nra_zero_product_cert::check_real_zero_product_refutation`]), which
//! re-scans the original assertions. That split is the same one the
//! hypothesis-binding audit already measures across the LRA routes; stating it
//! is not a disclaimer, it is the honest boundary.
//!
//! # Scope
//!
//! Slice 1 is the DIRECT form: exactly one zeroing case. The disjunctive form
//! (`(or (= v₁ 0) (= v₂ 0))`) needs case analysis in the kernel and is declined
//! rather than approximated — a partially covered split proves nothing, which is
//! precisely what the certificate's own checker refuses too.

use std::collections::BTreeMap;

use axeyum_lean_kernel::ExprId;

use super::{LraReconstructCtx, ReconstructError};
use crate::nra_zero_product_cert::RealZeroProductRefutationCertificate;

/// Multiset of factor names → occurrence count.
fn multiset(names: &[String]) -> BTreeMap<&str, usize> {
    let mut out: BTreeMap<&str, usize> = BTreeMap::new();
    for n in names {
        *out.entry(n.as_str()).or_insert(0) += 1;
    }
    out
}

/// The opaque `R`-typed constant standing for a source variable NAME.
///
/// Module-scope rather than nested inside the reconstruction: a `fn` declared
/// after a statement is `clippy::items_after_statements`, and this one shipped
/// that way — I read a clippy failure, saw another lane's errors above mine, and
/// stopped scrolling.
///
/// Indices are assigned in first-use order, which is the certificate's order,
/// which is sorted — so the emitted module is deterministic.
fn var_expr(
    ctx: &mut LraReconstructCtx,
    index_of: &mut BTreeMap<String, usize>,
    name: &str,
) -> ExprId {
    let next = index_of.len();
    let idx = *index_of.entry(name.to_owned()).or_insert(next);
    let n = ctx.var_const(idx);
    ctx.kernel.const_(n, vec![])
}

/// Reconstruct the direct monomial-divisibility refutation to `False`.
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] for the disjunctive form or when the
/// zeroed factors do not divide the non-zero ones (the certificate's own checker
/// already rejects the latter; this is a defensive re-check, because a
/// reconstruction that trusted the certificate would be reconstructing a claim
/// rather than checking one).
pub(crate) fn reconstruct_real_zero_product(
    ctx: &mut LraReconstructCtx,
    certificate: &RealZeroProductRefutationCertificate,
) -> Result<ExprId, ReconstructError> {
    let cases = certificate.zeroing_cases();
    let [zeroed] = cases else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "zero-product reconstruction handles the direct form (one zeroing case); \
                 this certificate has {} cases, which needs kernel case analysis",
                cases.len()
            ),
        });
    };
    let nonzero = certificate.nonzero_factors();

    // Re-establish divisibility here rather than trusting the certificate, and
    // compute the remaining factors `R`.
    let mut remaining = multiset(nonzero);
    for name in zeroed {
        match remaining.get_mut(name.as_str()) {
            Some(count) if *count > 0 => *count -= 1,
            _ => {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!(
                        "zeroed factor `{name}` does not divide the non-zero product; \
                         the certificate should not have been issued"
                    ),
                });
            }
        }
    }

    // A stable variable index per NAME, so the same name is the same opaque
    // constant throughout. Order is the certificate's, which is sorted, so the
    // emitted module is deterministic.
    let mut index_of: BTreeMap<String, usize> = BTreeMap::new();

    // `M` = product of the zeroed factors, left-associated.
    let mut m = var_expr(ctx, &mut index_of, zeroed[0].as_str());
    for name in &zeroed[1..] {
        let v = var_expr(ctx, &mut index_of, name.as_str());
        m = ctx.mk_mul(m, v);
    }

    // `R` = product of what remains. If nothing remains the two products are the
    // same term and the refutation is `h₂ h₁` directly.
    let rest: Vec<&str> = remaining
        .iter()
        .flat_map(|(name, count)| std::iter::repeat_n(*name, *count))
        .collect();

    let zero = ctx.mk_zero();
    let eq_m_zero = ctx.mk_eq_r(m, zero);
    let h1 = ctx.hyp_axiom(eq_m_zero)?;

    let (product, chain) = if rest.is_empty() {
        (m, h1)
    } else {
        let mut r = var_expr(ctx, &mut index_of, rest[0]);
        for name in &rest[1..] {
            let v = var_expr(ctx, &mut index_of, name);
            r = ctx.mk_mul(r, v);
        }
        let product = ctx.mk_mul(m, r);

        // M·R = 0·R
        let step1 = ctx.congr_mul_left(m, zero, r, h1);
        let zero_r = ctx.mk_mul(zero, r);
        // 0·R = R·0  (zero_mul is not in the prelude)
        let step2 = ctx.mul_comm_eq(zero, r);
        let r_zero = ctx.mk_mul(r, zero);
        // R·0 = 0
        let step3 = ctx.mul_zero_eq(r);

        let via = ctx.eq_trans_r(product, zero_r, r_zero, step1, step2);
        let chain = ctx.eq_trans_r(product, r_zero, zero, via, step3);
        (product, chain)
    };

    // h₂ : ¬(product = 0). `Not P` is `P → False`, so applying it closes.
    let eq_product_zero = ctx.mk_eq_r(product, zero);
    // Take `Not` from the signature's logic prelude, not by looking the string
    // up: a name resolved by text would silently mint a FRESH constant if the
    // prelude ever renamed it, and the hypothesis would then be about a
    // proposition nothing else mentions.
    let not_name = ctx.arith().logic.not;
    let not_const = ctx.kernel.const_(not_name, vec![]);
    let ne_product = ctx.kernel.app(not_const, eq_product_zero);
    let h2 = ctx.hyp_axiom(ne_product)?;
    let proof = ctx.kernel.app(h2, chain);

    // Soundness gate: the assembled term must kernel-infer to `False`. Without
    // this the function returns an `ExprId` nobody type-checked, which is how a
    // reconstruction claims success it has not earned.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "real_zero_product".to_owned(),
            detail: format!("zero-product infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "real_zero_product".to_owned(),
            detail: "zero-product refutation did not infer to False".to_owned(),
        })
    }
}

#[cfg(test)]
mod tests {
    //! The only claim that matters here is that the trusted kernel infers the
    //! assembled term to `False`. Everything else is bookkeeping.

    use super::*;
    use crate::nra_zero_product_cert::real_zero_product_refutation;
    use axeyum_smtlib::parse_script;

    /// `cli__regress1__nl__zero-subset.smt2`, in shape.
    const ZERO_SUBSET: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)\n\
        (declare-fun d () Real)(declare-fun e () Real)\n\
        (assert (= (* a b c d) 0))\n\
        (assert (not (= (* a b c d e) 0)))\n\
        (check-sat)";

    /// The degenerate case: the two products are the SAME, so `R` is empty and
    /// the refutation is the disequality applied to the equality directly.
    const IDENTICAL: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (= (* a b) 0))\n\
        (assert (not (= (* a b) 0)))\n\
        (check-sat)";

    /// The disjunctive form, which slice 1 declines rather than approximates.
    const DISJUNCTIVE: &str = "(set-logic QF_NRA)\n\
        (declare-fun v1 () Real)(declare-fun v2 () Real)(declare-fun v3 () Real)\n\
        (assert (or (= v1 0) (= v2 0)))\n\
        (assert (not (= (* v1 v2 v3) 0)))\n\
        (check-sat)";

    fn certificate(text: &str) -> RealZeroProductRefutationCertificate {
        let parsed = parse_script(text).expect("parses");
        real_zero_product_refutation(&parsed.arena, &parsed.assertions).expect("certificate")
    }

    /// **The measurement that decides whether any of this is worth having.**
    ///
    /// `LraReconstructCtx::new_over_axreal()` builds `AxReal` — the legacy AXIOMATIZED
    /// ordered field, 30 assumptions, the repository's only nonzero trusted-surface
    /// row. A refutation checked there rests on all 30. The constructed carrier
    /// `CReal` (ADR-0512) is a Bishop setoid over the constructed rationals at
    /// trusted surface **0**, and the shipped LRA/SOS routes already reconstruct
    /// over it (ADR-0509).
    ///
    /// So this asserts the refutation kernel-checks over the CONSTRUCTED reals,
    /// not merely over some ordered ring. Without it the module would be a
    /// 30-axiom proof wearing the same test name.
    #[test]
    fn the_refutation_kernel_checks_over_the_constructed_reals() {
        let (mut ctx, _adoption) = LraReconstructCtx::try_new_over_constructed_reals_reporting()
            .expect("the constructed real development builds");
        let proof = reconstruct_real_zero_product(&mut ctx, &certificate(ZERO_SUBSET))
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

    #[test]
    fn the_kernel_infers_the_refutation_to_false() {
        let mut ctx = LraReconstructCtx::new_over_axreal();
        let proof = reconstruct_real_zero_product(&mut ctx, &certificate(ZERO_SUBSET))
            .expect("reconstruction succeeds");
        // `reconstruct_real_zero_product` gates on this internally; assert it
        // again from outside so the gate cannot be deleted silently.
        let inferred = ctx.kernel_mut().infer(proof).expect("infer");
        let false_ = {
            let f = ctx.arith().logic.false_;
            ctx.kernel_mut().const_(f, vec![])
        };
        assert!(ctx.kernel_mut().def_eq(inferred, false_));
    }

    #[test]
    fn the_degenerate_equal_products_case_also_closes() {
        let mut ctx = LraReconstructCtx::new_over_axreal();
        let proof = reconstruct_real_zero_product(&mut ctx, &certificate(IDENTICAL))
            .expect("reconstruction succeeds");
        let inferred = ctx.kernel_mut().infer(proof).expect("infer");
        let false_ = {
            let f = ctx.arith().logic.false_;
            ctx.kernel_mut().const_(f, vec![])
        };
        assert!(ctx.kernel_mut().def_eq(inferred, false_));
    }

    #[test]
    fn the_disjunctive_form_is_declined_not_approximated() {
        let mut ctx = LraReconstructCtx::new_over_axreal();
        let result = reconstruct_real_zero_product(&mut ctx, &certificate(DISJUNCTIVE));
        assert!(
            matches!(result, Err(ReconstructError::UnsupportedTerm { .. })),
            "a two-case split needs kernel case analysis; got {result:?}"
        );
    }

    #[test]
    fn a_certificate_whose_factors_do_not_divide_is_refused() {
        // Defensive: the certificate's own checker rejects this, so it should
        // never reach here — but a reconstruction that TRUSTED the certificate
        // would be reconstructing a claim rather than checking one.
        let mut cert = certificate(ZERO_SUBSET);
        let forged = RealZeroProductRefutationCertificate::testing_from_parts(
            vec![vec!["zzz".to_owned()]],
            cert.nonzero_factors().to_vec(),
        );
        cert = forged;
        let mut ctx = LraReconstructCtx::new_over_axreal();
        let result = reconstruct_real_zero_product(&mut ctx, &cert);
        assert!(matches!(
            result,
            Err(ReconstructError::UnsupportedTerm { .. })
        ));
    }
}

#[cfg(test)]
mod end_to_end {
    //! The route as a caller sees it: query in, Lean module out.

    use crate::reconstruct::{ProofFragment, scan_proof_fragment};
    use axeyum_smtlib::parse_script;

    const ZERO_SUBSET: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)\n\
        (declare-fun d () Real)(declare-fun e () Real)\n\
        (assert (= (* a b c d) 0))\n\
        (assert (not (= (* a b c d e) 0)))\n\
        (check-sat)";

    #[test]
    fn the_query_classifies_as_a_theory_reconstruction_not_an_attestation() {
        let p = parse_script(ZERO_SUBSET).expect("parses");
        assert_eq!(
            scan_proof_fragment(&p.arena, &p.assertions),
            ProofFragment::RealZeroProduct,
            "must not fall through to the NraEvenPower attestation tier"
        );
    }

    #[test]
    fn the_front_door_emits_a_kernel_checked_lean_module() {
        let mut p = parse_script(ZERO_SUBSET).expect("parses");
        let assertions = p.assertions.clone();
        let (fragment, module) =
            crate::reconstruct::prove_unsat_to_lean_module(&mut p.arena, &assertions)
                .expect("a Lean module is produced");
        assert_eq!(fragment, ProofFragment::RealZeroProduct);
        assert!(!module.is_empty());
        // The module must carry THIS refutation's ring reasoning, not a generic
        // wrapper asserting the conclusion.
        assert!(
            module.contains("mul"),
            "the module should contain the ring reasoning; got:\n{module}"
        );
    }
}
