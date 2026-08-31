//! Gauss's lemma's sign-product identity: `∏_{k=1}^m ε_k = (-1)^gaussNegCount(pp,a,m)`,
//! where `ε_k := -1` when `Nat.gaussSignNeg pp a k` is `true` and `ε_k := 1`
//! otherwise. `nat_prelude/gauss_lemma.rs`'s own module doc names this as the
//! one piece of Gauss's lemma's connecting-theorem assembly with "no existing
//! analogue found" (ADR-0990's "product of signs equals `(-1)^count`" item).
//!
//! It is a one-line corollary of `Int.prodRangeIf_constEqPowCount`
//! (`euler_theorem.rs`, built generically because Euler's theorem needs the
//! identical shape at an arbitrary constant), instantiated at:
//!
//! - `pred := fun j => Nat.gaussSignNeg pp a (succ j)` -- the EXACT lambda
//!   `Nat.gaussNegCount`'s own `Definition` body uses
//!   (`gauss_lemma.rs::declare_gauss_neg_count`), so `Nat.countRange pred m`
//!   is defeq `Nat.gaussNegCount pp a m` with no further lemma or rewrite;
//! - `a := Int.neg Int.one`.
//!
//! No induction is written here at all -- the whole proof is one application
//! of the general theorem, with the kernel's own defeq closing both the
//! `prodRangeIf`-unfolds-to-`prodRange`-with-a-beta-reduced-selector gap and
//! the `countRange`-unfolds-to-`gaussNegCount` gap.
//!
//! ## What this does NOT reach
//!
//! This is one of the FIVE pieces `docs/research/09-decisions/adr-0990-…md`
//! sizes for Gauss's lemma's connecting theorem (`a^m ≡ (-1)^gaussNegCount
//! [pp]`, the theorem's actual content). The other four -- the
//! `∏(a·k) = a^m·m!` identity, the per-term `Nat`/`Int` congruence bridging
//! `a·k` to `ε_k·gaussFold(pp,a,k)`, `gcd(m!,pp) = 1`, and the final
//! assembly/cancellation -- are NOT attempted here. See this lane's status
//! doc (`docs/plan/status/gauss-piece-3.md`) for the precise route and what
//! each remaining piece needs.

use super::ops::IntDev;
use super::prod::bool_select_int;
use crate::KernelError;
use crate::nat_prelude::NatOps;

/// `Int.gaussSignProdEqPowNegOneOfCount :
///   ∀ pp a m, Eq Int
///     (prodRange (fun j => bool_select_int (Nat.gaussSignNeg pp a (succ j))
///       (neg one) one) m)
///     (pow (neg one) (Nat.gaussNegCount pp a m))`
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gauss_sign_prod_eq_pow_neg_one_of_count(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // pred := fun j => Nat.gaussSignNeg pp a (succ j) -- the identical
    // lambda `Nat.gaussNegCount`'s own definition uses.
    let pred = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let body = d.const_app(p.nat.gauss_sign_neg, &[pp, a, sj]);
        d.lam_fv(j_fv, nat, body)
    };

    let one_i = d.ione();
    let neg_one = d.ineg(one_i);

    let stmt = {
        let selector = {
            let j2_fv = d.fresh_fvar();
            let j2 = d.kernel().fvar(j2_fv);
            let pj = d.apply(pred, &[j2]);
            let sel = bool_select_int(d, pj, neg_one, one_i);
            d.lam_fv(j2_fv, nat, sel)
        };
        let lhs = d.const_app(p.prod_range, &[selector, m]);
        let count = d.const_app(p.nat.gauss_neg_count, &[pp, a, m]);
        let rhs = d.ipow(neg_one, count);
        d.ieq(lhs, rhs)
    };

    let proof = d.lemma(p.prod_range_if_const_eq_pow_count, &[pred, neg_one, m]);

    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt);
        let with_a = d.pi_fv(a_fv, nat, with_m);
        d.pi_fv(pp_fv, nat, with_a)
    };
    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_a = d.lam_fv(a_fv, nat, with_m);
        d.lam_fv(pp_fv, nat, with_a)
    };
    d.declare_theorem(p.gauss_sign_prod_eq_pow_neg_one_of_count, ty, value)
}
