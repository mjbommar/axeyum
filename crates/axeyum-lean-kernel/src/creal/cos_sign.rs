//! Toward `cos (8/5) < 0` — π's rung 2 (`docs/plan/status/169-pi.md`).
//!
//! This file carries the general theorems that rung 2 needs and that nothing
//! in the tree had. Neither mentions cosine.
//!
//! ## 1. [`declare_converges_upper_bound_shift`] — `CReal.converges_upper_bound_shift`
//!
//! `∀ s f L b, (∀ n, le (f (Nat.add n s)) b) → Converges f L → le L b`: the
//! EVENTUAL upper bound, the mirror of
//! [`CRealPrelude::converges_lower_bound_shift`].
//! `creal/alternating.rs::declare_alternating_upper_bound`'s own doc comment
//! records that "this development has no `converges_upper_bound_shift`" and
//! then performs the negation route INLINE, privately, on its own concrete
//! sequence — hiding place 2 of `CLAUDE.md`'s retrieval section, one
//! declaration away from being reusable. It is that route, lifted to a named,
//! general theorem: `neg_le_neg` turns the eventual upper bound into an
//! eventual LOWER bound on the negated sequence, `converges_neg` supplies the
//! negated limit, [`CRealPrelude::converges_lower_bound_shift`] closes `le
//! (neg b) (neg L)`, and one more `neg_le_neg` plus `double_neg` on each side
//! (`le_congr`) flips it back.
//!
//! ## 2. [`declare_alternating_upper_bound_tail`] — `CReal.alternatingUpperBoundTail`
//!
//! The Leibniz upper bound requiring antitonicity only **from index 1**:
//!
//! ```text
//! ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a (succ (succ k))) (a (succ k))) →
//!   ∀ L, Converges (sumRange (fun k => mul (pow (neg one) k) (a k))) L →
//!     le L (sumRange (fun k => mul (pow (neg one) k) (a k)) 3)
//! ```
//!
//! [`CRealPrelude::alternating_upper_bound`] cannot be pointed at cosine's
//! series at `8/5`, and the reason is arithmetic rather than formal: its
//! `hdec` premise is the GLOBAL `∀ k, a (succ k) ≤ a k`, and cosine's
//! magnitude sequence `a k = (8/5)^{2k}/(2k)!` has `a 0 = 1 < a 1 = 32/25`.
//! The tail from `k = 1` is antitone (`a (k+1)/a k = (64/25)/((2k+1)(2k+2)) ≤
//! (64/25)/12 < 1` for `k ≥ 1`), which is exactly this theorem's hypothesis.
//!
//! **The route is a CLAMP, not a shift**, and that choice is the whole reason
//! this is tractable. `169-pi.md` proposed re-indexing the series by one
//! (`b k := a (k+1)`, limit `T = 1 − cos(8/5)`); that needs a `Converges`
//! witness for a series this development does not have one for, and building
//! it runs into `Converges`'s own index-`0` obligation, which no "eventually
//! equal" bridge can discharge for an arbitrary sequence. Instead, define
//!
//! ```text
//! â k := a (Nat.succ (Nat.pred k))
//! ```
//!
//! — `a` with its index-`0` value REPLACED by its index-`1` value, chosen in
//! that spelling because `Nat.pred` makes both halves free: `â 0 ≡ a 1` and
//! `â (succ j) ≡ a (succ j)`, both by `ι` alone. `â` IS globally antitone (at
//! `k = 0` by `le_refl`, and at `k = succ j` by the tail hypothesis), so
//! [`CRealPrelude::alternating_bracket_upper`] applies to it unchanged. Its
//! partial sums differ from `a`'s by the single CONSTANT `c := a 1 − a 0` at
//! every index `≥ 1` ([`sum_shift_identity`], one induction), so the constant
//! cancels off both sides of the bracket's conclusion and what survives is a
//! statement about `a`'s OWN partial sums — whose `Converges` witness is the
//! hypothesis in hand. [`declare_converges_upper_bound_shift`] then closes the
//! limit at shift `s := 2`.

use super::convergence::converges_applied;
use super::trig::{cle, cneg, double_neg};
use super::{CRealPrelude, creal_ty};
use crate::KernelError;
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

// ---------------------------------------------------------------------------
// `CReal.converges_upper_bound_shift`.
// ---------------------------------------------------------------------------

/// `CReal.converges_upper_bound_shift`. See
/// [`CRealPrelude::converges_upper_bound_shift`] and this module's own
/// documentation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_converges_upper_bound_shift(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = d.arrow(nat, carrier);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let upper_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let shifted = NatOps::add(d, n, s);
        let f_at = d.apply(f, &[shifted]);
        let claim = cle(d, p, f_at, b);
        d.pi_fv(n_fv, nat, claim)
    };
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target_ty = cle(d, p, l, b);

    // shift_hyp : ∀ n, le (neg b) (neg (f (add n s))) -- exactly the shape
    // `converges_lower_bound_shift` wants for the NEGATED sequence.
    let neg_b = cneg(d, p, b);
    let shift_hyp = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let shifted = NatOps::add(d, n, s);
        let f_at = d.apply(f, &[shifted]);
        let at_n = d.apply(h1, &[n]);
        let flipped = d.lemma(p.neg_le_neg, &[f_at, b, at_n]);
        d.lam_fv(n_fv, nat, flipped)
    };

    let neg_f_lam = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_n = d.apply(f, &[n]);
        let neg_f_n = cneg(d, p, f_n);
        d.lam_fv(n_fv, nat, neg_f_n)
    };
    let neg_l = cneg(d, p, l);
    let converges_neg_hyp = d.const_app(p.converges_neg, &[f, l, h2]);
    let lower = d.const_app(
        p.converges_lower_bound_shift,
        &[s, neg_b, neg_f_lam, neg_l, shift_hyp, converges_neg_hyp],
    );
    // lower : le (neg b) (neg L)

    let flipped_back = d.lemma(p.neg_le_neg, &[neg_b, neg_l, lower]);
    // flipped_back : le (neg (neg L)) (neg (neg b))
    let nn_l = cneg(d, p, neg_l);
    let nn_b = cneg(d, p, neg_b);
    let dn_l = double_neg(d, p, l);
    let dn_b = double_neg(d, p, b);
    let result = d.lemma(p.le_congr, &[nn_l, l, nn_b, b, dn_l, dn_b, flipped_back]);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_fl, result);
        let with_h1 = d.lam_fv(h1_fv, upper_ty, with_h2);
        let with_b = d.lam_fv(b_fv, carrier, with_h1);
        let with_l = d.lam_fv(l_fv, carrier, with_b);
        let with_f = d.lam_fv(f_fv, seq_ty, with_l);
        d.lam_fv(s_fv, nat, with_f)
    };
    let ty = {
        let after_h2 = d.arrow(converges_fl, target_ty);
        let after_h1 = d.arrow(upper_ty, after_h2);
        let with_b = d.pi_fv(b_fv, carrier, after_h1);
        let with_l = d.pi_fv(l_fv, carrier, with_b);
        let with_f = d.pi_fv(f_fv, seq_ty, with_l);
        d.pi_fv(s_fv, nat, with_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_upper_bound_shift,
        uparams: vec![],
        ty,
        value,
    })
}
