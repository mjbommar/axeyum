//! `Nat.multichoose n k` — the number of size-`k` multisets drawn from an
//! `n`-element type — defined directly in terms of
//! [`NatPrelude::choose`](super::NatPrelude::choose) rather than by a fresh
//! recursion:
//!
//! ```text
//! multichoose n k := choose (pred (add n k)) k
//! ```
//!
//! i.e. `n.multichoose k = (n + k - 1).choose k`, using
//! [`NatOps::pred`] rather than [`NatOps::sub`] to reach `n + k - 1`:
//! `Nat.sub x 1` itself reduces (two `ι` steps, `sub x (succ zero) ≡ pred
//! (sub x zero) ≡ pred x`) to `Nat.pred x`, so `pred` is the more direct
//! spelling and needs no extra unfold.
//!
//! This is **not** a new recursion at all — `multichoose` is a plain
//! (non-recursive) abbreviation over already-declared `Nat.add`, `Nat.pred`
//! and `Nat.choose`, so `add_declaration` only has to check that the lambda
//! type-checks. Every boundary lemma below is proved by reducing the
//! abbreviation and reaching for an existing `choose` theorem
//! ([`NatPrelude::choose_zero_right`](super::NatPrelude::choose_zero_right),
//! [`NatPrelude::choose_self`](super::NatPrelude::choose_self),
//! [`NatPrelude::choose_one_right`](super::NatPrelude::choose_one_right))
//! rather than by induction on `multichoose` itself:
//!
//!   * [`declare_multichoose_zero_right`] — `n.multichoose 0 = 1` for
//!     **any** `n`, since `choose_zero_right` holds for any first argument;
//!     needs no reduction of `pred (add n 0)` at all.
//!   * [`declare_multichoose_one`] — `Nat.multichoose 1 k = 1`; `Nat.add`
//!     recurses on its RIGHT argument, so `add 1 k` is stuck for symbolic
//!     `k` and needs `succ_add`/`zero_add` to reach `succ k`, then
//!     `pred (succ k) ≡ k` by ι and `choose_self` closes it.
//!   * [`declare_multichoose_one_right`] — `n.multichoose 1 = n`; here the
//!     literal `1` sits on `add`'s RIGHT (recursive) side, so `add n 1 ≡
//!     succ n` and `pred (succ n) ≡ n` reduce fully by ι with **no lemma at
//!     all**, and `choose_one_right` closes `choose n 1 = n` directly.
//!
//! A `Definition` type-checks whatever value it computes — `Nat → Nat →
//! Nat` is `Nat → Nat → Nat` regardless of whether the body is right —
//! so `nat_prelude_tests::multichoose_evaluates_correctly` checks concrete
//! values independently of any of the three theorems above: `multichoose 0
//! 0 = choose (pred (add 0 0)) 0 = choose 0 0 = 1` (the empty multiset), and
//! `multichoose 3 2 = choose 4 2 = 6` (the six size-2 multisets of `{a,b,c}`:
//! `aa, ab, ac, bb, bc, cc`), with a negative control that `choose (add n k)
//! k` (omitting `pred`, i.e. off by the `-1`) gives a DIFFERENT value at the
//! same arguments (`choose 5 2 = 10 ≠ 6`) — catching a dropped `pred` that
//! would still type-check.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.multichoose n k`.
fn multichoose(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.multichoose, &[n, k])
}

/// `Nat.multichoose : Nat → Nat → Nat := fun n k => choose (pred (add n k)) k`.
///
/// Not a recursion — a plain abbreviation over already-declared `Nat.add`,
/// `Nat.pred` and `Nat.choose` — so `add_declaration` only type-checks the
/// lambda. Strictly greater delta height than all three (`choose` is the
/// tallest, at `2`).
pub(super) fn declare_multichoose(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sum = d.add(n, k);
    let pred_sum = d.pred(sum);
    let body = d.choose(pred_sum, k);
    let value = {
        let inner = d.lam_fv(k_fv, nat, body);
        d.lam_fv(n_fv, nat, inner)
    };
    let ty = {
        let inner = d.arrow(nat, nat);
        d.arrow(nat, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.multichoose,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(())
}

/// `multichoose_zero_right : ∀ n, n.multichoose 0 = 1`.
///
/// `n.multichoose 0` reduces (β/δ) to `choose (pred (add n 0)) 0`, and
/// `choose_zero_right` proves `choose _ 0 = 1` for **any** first argument —
/// so instantiating it at `pred (add n 0)` closes the goal directly, with no
/// need to know what that expression reduces to.
pub(super) fn declare_multichoose_zero_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.multichoose_zero_right, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let lhs = multichoose(d, &p, n, zero);
        let one = d.num(1);
        let sum = d.add(n, zero);
        let pred_sum = d.pred(sum);
        let proof = d.lemma(p.choose_zero_right, &[pred_sum]);
        (d.eq(lhs, one), proof)
    })?;
    Ok(())
}

/// `multichoose_one : ∀ k, Nat.multichoose 1 k = 1`.
///
/// `1.multichoose k` reduces to `choose (pred (add 1 k)) k`, and `add 1 k`
/// does **not** reduce on its own — `Nat.add` recurses on its RIGHT
/// argument, so a literal on the LEFT leaves it stuck for symbolic `k`.
/// Bridged via `succ_add (0, k) : add (succ 0) k = succ (add 0 k)` then
/// `zero_add k : add 0 k = k`, giving `add 1 k = succ k`; `pred (succ k)`
/// then reduces to `k` by ι alone, and `choose_self` closes `choose k k =
/// 1`.
pub(super) fn declare_multichoose_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.multichoose_one, 1, &|d, v| {
        let k = v[0];
        let one = d.num(1);

        let add1k = d.add(one, k);
        let succ_k = d.succ(k);

        // add (succ 0) k = succ (add 0 k)
        let zero = d.zero();
        let succ_add_0k = d.lemma(p.succ_add, &[zero, k]);
        let add0k = d.add(zero, k);
        let succ_add0k = d.succ(add0k);

        // add 0 k = k, lifted through `succ`
        let zero_add_k = d.lemma(p.zero_add, &[k]);
        let h_congr = d.congr(add0k, k, zero_add_k, &|d, x| d.succ(x));

        let (_last, add1k_eq_succk) =
            d.chain(add1k, &[(succ_add0k, succ_add_0k), (succ_k, h_congr)]);

        // pred (add 1 k) = pred (succ k), then defeq-coerced to `= k`
        // (`pred (succ k)` reduces to `k` by ι alone).
        let pred_add1k = d.pred(add1k);
        let pred_succk = d.pred(succ_k);
        let h_pred = d.congr(add1k, succ_k, add1k_eq_succk, &|d, x| d.pred(x));
        let refl_k = d.refl(pred_succk);
        let pred_add1k_eq_k = d.trans(pred_add1k, pred_succk, k, h_pred, refl_k);

        // choose (pred (add 1 k)) k = choose k k, then choose_self k : = 1
        let lhs_choose = d.choose(pred_add1k, k);
        let choose_kk = d.choose(k, k);
        let h_choose = d.congr(pred_add1k, k, pred_add1k_eq_k, &|d, x| d.choose(x, k));
        let choose_self_k = d.lemma(p.choose_self, &[k]);
        let (_last2, proof) =
            d.chain(lhs_choose, &[(choose_kk, h_choose), (one, choose_self_k)]);

        let lhs = multichoose(d, &p, one, k);
        (d.eq(lhs, one), proof)
    })?;
    Ok(())
}

/// `multichoose_one_right : ∀ n, n.multichoose 1 = n`.
///
/// `n.multichoose 1` reduces (β/δ) to `choose (pred (add n 1)) 1`, and `add
/// n 1 ≡ add n (succ zero) ≡ succ (add n zero) ≡ succ n` reduces fully by ι
/// alone (the literal `1` sits on `Nat.add`'s right/recursive side, and
/// `add n zero ≡ n` is its base case, holding for any `n`) — then `pred
/// (succ n) ≡ n` reduces the same way, so the whole index collapses to `n`
/// with **no lemma at all**, and `choose_one_right` closes `choose n 1 = n`
/// directly — mirroring
/// [`super::desc_factorial::declare_desc_factorial_one`]'s "the goal is
/// already defeq to an existing lemma's stated type" shape.
pub(super) fn declare_multichoose_one_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.multichoose_one_right, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let lhs = multichoose(d, &p, n, one);
        let proof = d.lemma(p.choose_one_right, &[n]);
        (d.eq(lhs, n), proof)
    })?;
    Ok(())
}

/// Declare [`declare_multichoose`], then its three boundary lemmas —
/// [`declare_multichoose_zero_right`], [`declare_multichoose_one`],
/// [`declare_multichoose_one_right`] — which depend only on `Nat.choose`'s
/// own theorems (`choose_zero_right`, `choose_self`, `choose_one_right`),
/// declared far earlier in the prelude build.
pub(super) fn declare_multichoose_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_multichoose(d, p)?;
    declare_multichoose_zero_right(d, p)?;
    declare_multichoose_one(d, p)?;
    declare_multichoose_one_right(d, p)?;
    Ok(())
}
