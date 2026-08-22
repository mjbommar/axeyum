//! The **Archimedean property of `CReal`** (ADR-0512 phase R5): every real is
//! below some natural number, embedded.
//!
//! ## Why this is nearly free
//!
//! [`CReal.bound_within`](super::CRealPrelude::bound_within) already proves,
//! for **every** index `m` at once, `Within (seq x m) ((bound x + 1)/1)` — a
//! single rational bound on every sample of `x`'s representative, established
//! from regularity at index `0` alone (see `product.rs`). `CReal.le x y`
//! asks for exactly one inequality per index, `seq x n − seq y n ≤ 2/(n+1)`,
//! so `bound_within`'s upper half is already the stronger statement: taking
//! `y := ofNat (bound x + 1)` makes `seq y n` the *same* rational at every
//! `n`, and `seq x n − seq y n ≤ 0 ≤ 2/(n+1)` needs no index-by-index
//! argument, no case split on `x`'s sign, and no search over witnesses.
//!
//! That is also why this module does not need the Archimedean property of
//! `ℚ` again: `RatPrelude`'s `le_of_le_add_natDivSucc` earns its keep in
//! `Equiv.trans`, `le_trans` and `bound_within` (comparing samples at two
//! *different* indices, which forces a third to be chosen); here both sides
//! of `CReal.le` are compared **at the same index**, so the estimate is
//! exact and elementary — `Rat.add_le_add` and `Rat.sub_le_of_le` close it.
//!
//! ## `CReal.ofNat` reuses `Rat.natDivSucc`, deliberately
//!
//! `Rat.natDivSucc k j` is already `k/(j+1)` for a `Nat` numerator `k`, so
//! `Rat.natDivSucc n 0` is `n/1` — a second `ℕ ↪ ℚ` embedding would duplicate
//! it for no reason. `CReal.ofNat n := CReal.ofRat (Rat.natDivSucc n 0)` is
//! the whole definition, and it is what lets the witness proof below share
//! its central term, `Rat.natDivSucc (CReal.bound x + 1) 0`, verbatim with
//! [`CReal.bound_within`](super::CRealPrelude::bound_within)'s own bound.

use super::{CRealPrelude, DERIVED_HEIGHT, cle, creal_ty, embed, halves, sample};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rle, rzero};

/// Admit `CReal.ofNat` and `CReal.archimedean`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_archimedean(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_of_nat(d, p)?;
    declare_archimedean_property(d, p)
}

/// `Rat.natDivSucc k j`, with a **symbolic** `Nat` numerator `k` (unlike
/// [`super::div_succ`], which only takes a literal).
fn div_succ_at(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `CReal.bound x`.
fn bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.bound, &[x])
}

/// `CReal.ofNat n`.
fn of_nat(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    d.const_app(p.of_nat, &[n])
}

/// `CReal.ofNat n := CReal.ofRat (Rat.natDivSucc n 0)`.
fn declare_of_nat(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let result = creal_ty(d, p);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let zero_nat = d.num(0);
    let rational = div_succ_at(d, p, n, zero_nat);
    let embedded = embed(d, p, rational);
    let value = d.lam_fv(n_fv, nat, embedded);
    let ty = d.arrow(nat, result);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.of_nat,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 14),
    })
}

/// `CReal.archimedean : ∀ x, ∃ n, CReal.le x (CReal.ofNat n)`.
///
/// Witness `n := CReal.bound x + 1`; then `CReal.ofNat n`'s representative is
/// the constant `Rat.natDivSucc (CReal.bound x + 1) 0`, the exact bound
/// [`CReal.bound_within`](super::CRealPrelude::bound_within) supplies at every
/// index. The body of the `∀ k` inside `CReal.le` is then:
///
/// ```text
/// seq x k − target ≤ 0                     (bound_within's upper half, widened)
///                  ≤ 2/(k+1)                (Rat.sub_le_of_le, folding the 0)
/// ```
///
/// closed by `Rat.add_le_add`/`Rat.add_zero` (to get `target ≤ target +
/// 2/(k+1)`) and `Rat.sub_le_of_le` (to fold the addition back into a
/// subtraction) — no estimate specific to `x`, and no Archimedean lemma over
/// `ℚ` is consumed a second time.
fn declare_archimedean_property(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let one = d.level_one();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    // The witness: `n := CReal.bound x + 1`.
    let magnitude = bound_of(d, p, x);
    let witness = d.succ(magnitude);
    let target = {
        let zero_nat = d.num(0);
        div_succ_at(d, p, witness, zero_nat)
    };

    // `∀ k, seq x k − target ≤ 2/(k+1)` — the body `CReal.le x (ofNat witness)`
    // unfolds to, `seq (ofNat witness) k` reducing to `target` at every `k`.
    let le_proof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let point = sample(d, p, x, k);
        let bw = d.lemma(p.bound_within, &[x, k]);
        let (_, upper) = halves(d, p, point, target, bw);

        let two_nat = d.num(2);
        let bound2 = div_succ_at(d, p, two_nat, k);
        let nonneg2 = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, k]);

        // `target + 0 ≤ target + 2/(k+1)`, then fold `target + 0 = target`.
        let zero = rzero(d, rat);
        let target_refl = d.lemma(rat.le_refl, &[target]);
        let widened = d.lemma(
            rat.add_le_add,
            &[target, target, zero, bound2, target_refl, nonneg2],
        );
        let padded_target = radd(d, target, zero);
        let sum = radd(d, target, bound2);
        let trim = d.lemma(rat.add_zero, &[target]);
        let target_le_sum = rat_eq_rewrite(d, padded_target, target, trim, widened, &|d, t| {
            rle(d, rat, t, sum)
        });

        // `seq x k ≤ target ≤ target + 2/(k+1)`, so `seq x k ≤ target + 2/(k+1)`.
        let chained = d.lemma(rat.le_trans, &[point, target, sum, upper, target_le_sum]);

        // `Rat.sub_le_of_le : u ≤ v + q → u − v ≤ q`.
        let at_index = d.lemma(rat.sub_le_of_le, &[point, target, bound2, chained]);
        d.lam_fv(k_fv, nat, at_index)
    };

    // `∃ n, CReal.le x (CReal.ofNat n)`.
    let predicate = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let target_n = of_nat(d, p, n);
        let body = cle(d, p, x, target_n);
        d.lam_fv(n_fv, nat, body)
    };
    let exists_name = p.rat.int.logic.exists_;
    let exists_intro_name = p.rat.int.logic.exists_intro;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    let stmt = d.apply(exists_const, &[nat, predicate]);
    let intro = d.kernel().const_(exists_intro_name, vec![one]);
    let witnessed = d.apply(intro, &[nat, predicate, witness, le_proof]);

    let value = d.lam_fv(x_fv, carrier, witnessed);
    let ty = d.pi_fv(x_fv, carrier, stmt);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.archimedean,
        uparams: vec![],
        ty,
        value,
    })
}
