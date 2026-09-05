//! **ADR-1540's / ADR-1544's residue 2: the residue/fold reconciliation.**
//!
//! ```text
//! Nat.leastResidue_sumRange_reconcile : ∀ ap a m,
//!   Eq (add (sumRange (fun j => leastResidue (succ ap) a (succ j)) m)
//!           (add (sumRangeIf sign fold m) (sumRangeIf sign fold m)))
//!      (add (sumRange (fun j => gaussFold (succ ap) a (succ j)) m)
//!           (mul (succ ap) (gaussNegCount (succ ap) a m)))
//! ```
//!
//! with `sign j := gaussSignNeg (succ ap) a (succ j)` and
//! `fold j := gaussFold (succ ap) a (succ j)`.
//!
//! ## What it says, and why it is spelled additively
//!
//! Both prior lanes wrote the residue as
//! `Σ leastResidue = Σ gaussFold + pp·N − 2·Σ_neg gaussFold`. That
//! statement cannot be made here as written: `Nat.sub` is TRUNCATED, so an
//! identity with a subtraction on the right is a different proposition from
//! the one intended whenever the subtrahend could exceed the minuend, and
//! nothing in the statement bounds it. Moving the negative term to the other
//! side removes the question entirely — `Σ leastResidue + 2·Σ_neg gaussFold
//! = Σ gaussFold + pp·N` is the same identity over ℤ and is unambiguous over
//! ℕ. The doubling is written `x + x` rather than `2 * x` for the same
//! reason a `succ` divisor is preferred to a positivity hypothesis: `mul 2 x`
//! is stuck at a symbolic `x` (`Nat.mul` recurses on its RIGHT argument), so
//! `2 * Σ` would need a `two_mul` bridge this prelude does not have.
//!
//! ## Why there is NO hypothesis
//!
//! The identity is pointwise, and it holds at every index for every `a` —
//! coprimality is what makes the FOLD a bijection (`gauss_fold_sumRange_eq`,
//! ADR-1544 §5), not what makes a residue and its reflection add up. The
//! only side condition the argument needs is `leastResidue < pp`, which is
//! `Nat.mod_lt` at a positive modulus, and the modulus is given
//! constructively as `succ ap` so the positivity is `Nat.zero_lt_succ` and
//! never becomes a hypothesis. This is the same "divisors are `succ`"
//! convention ADR-1544 §2 records for `Nat.eisenstein_floor_sum`.
//!
//! A consequence worth stating plainly, because it is the opposite of what
//! the earlier handoffs implied: **residue 2 was never blocked on Gauss's
//! lemma or on coprimality.** It was blocked on `Nat.sumRangeIf`, which did
//! <!-- was-absent: Nat.sumRangeIf -->
//! not exist, and on nothing else.
//!
//! ## The proof
//!
//! One pointwise fact lifted by three general sum laws that already existed:
//!
//! 1. **Pointwise**, at `k := succ j`, writing `L := leastResidue pp a k`,
//!    `b := gaussSignNeg pp a k`, `G := gaussFold pp a k`:
//!
//!    ```text
//!    L + (sel b G 0 + sel b G 0) = G + pp * sel b 1 0
//!    ```
//!
//!    A single `Bool.rec` on `b` — but note that `G` itself is
//!    `bool_select_nat b (sub pp L) L` by δ, so the motive has to abstract
//!    BOTH occurrences of `b`, the one in the selector and the one inside
//!    `gaussFold`. That is why the motive is written over
//!    `bool_select_nat x (bool_select_nat x (sub pp L) L) 0` and not over
//!    `gaussFold` (which has no `x` to abstract).
//!
//!    - `b = false`: every selector is `0`, both sides reduce to `L` by ι
//!      and `Nat.add`/`Nat.mul`'s own right-argument rules — `Eq.refl`.
//!    - `b = true`: the goal is `L + (G + G) = G + pp * 1` with
//!      `G ≡ sub pp L`. Closed by `Nat.add_sub_cancel_of_le` (which needs
//!      `Le L pp`, from `Nat.mod_lt` + `le_of_lt`), `Nat.mul_one`,
//!      `Nat.add_assoc` and `Nat.add_comm`. The truncated subtraction never
//!      has to be reasoned about directly: `add_sub_cancel_of_le` is exactly
//!      the lemma that makes `L + (pp − L)` equal `pp` under `L ≤ pp`.
//!
//! 2. **Lifted** by `Nat.sumRange_congr` (unbounded — the pointwise fact has
//!    no index restriction), then `Nat.sumRange_add` three times to split the
//!    two sides into their summands, `Nat.mul_sumRange` to pull `pp` out of
//!    the indicator sum, and `Nat.countRange_eq_sumRange` to name that
//!    indicator sum as `Nat.countRange` — which at this predicate IS
//!    `Nat.gaussNegCount` by δ, with no bridging step.
//!
//! Nothing here is `Int`-valued and nothing is lifted; the whole statement
//! lives in `Nat`, which is where `eisenstein_lattice.rs` works.
//!
//! ## What this does NOT prove
//!
//! **Eisenstein's lemma is not proved, and neither is quadratic
//! reciprocity.** This closes residue 2 only. Residue 3 — the mod-2
//! bookkeeping over `Int.sumRange`/`Int.modEq_sumRange`, which turns this
//! `Nat` identity into a congruence mod 2 relating `gaussNegCount` to the
//! floor sum — is untouched here.

use super::NatPrelude;
use super::finite::le_of_lt;
use super::gauss_lemma::{gauss_fold, gauss_neg_count, gauss_sign_neg, least_residue};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `fun j => body(succ j)`, the one-based shift every index function here
/// shares.
fn shifted(d: &mut NatDev<'_>, body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let sj = d.succ(j);
    let b = body(d, sj);
    d.lam_fv(j_fv, nat, b)
}

/// The pointwise identity, at one index `k`:
/// `L + (sel b G 0 + sel b G 0) = G + pp * sel b 1 0`, where `L` is the least
/// residue, `b` the sign and `G` the fold at `k`.
///
/// See the module doc for why the motive abstracts `b` twice.
fn pointwise(d: &mut NatDev<'_>, p: &NatPrelude, ap: ExprId, a: ExprId, k: ExprId) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let pp = d.succ(ap);

    let lr = least_residue(d, &p_, pp, a, k);
    let sign = gauss_sign_neg(d, &p_, pp, a, k);
    let diff = d.sub(pp, lr);

    // `fun x : Bool => Eq (add L (add (sel x (sel x diff L) 0)
    //                                 (sel x (sel x diff L) 0)))
    //                     (add (sel x diff L) (mul pp (sel x 1 0)))`
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fold_x = d.bool_select_nat(x, diff, lr);
        let zero_a = d.zero();
        let sel_a = d.bool_select_nat(x, fold_x, zero_a);
        let zero_b = d.zero();
        let sel_b = d.bool_select_nat(x, fold_x, zero_b);
        let doubled = d.add(sel_a, sel_b);
        let lhs = d.add(lr, doubled);
        let one = d.num(1);
        let zero_c = d.zero();
        let ind = d.bool_select_nat(x, one, zero_c);
        let scaled = d.mul(pp, ind);
        let rhs = d.add(fold_x, scaled);
        let stmt = d.eq(lhs, rhs);
        d.lam_fv(x_fv, bool_ty, stmt)
    };

    // `b = false`: both sides ι-reduce to `L` (`add L 0 ≡ L`,
    // `mul pp 0 ≡ 0`), so this really is a bare `Eq.refl`.
    let case_false = d.refl(lr);

    // `b = true`: `L + (G + G) = G + pp*1` with `G ≡ sub pp L`.
    let case_true = {
        // `Le L pp`, from `mod_lt` at the positive modulus. The positivity
        // is `zero_lt_succ ap`, never a hypothesis -- the modulus is given
        // constructively as `succ ap`.
        let le_lr_pp = {
            let prod = d.mul(a, k);
            let pos_pp = d.zero_lt_succ(ap);
            let lt = d.lemma(p_.mod_lt, &[prod, pp, pos_pp]);
            le_of_lt(d, &p_, lr, pp, lt)
        };
        let add_cancel = d.lemma(p_.add_sub_cancel_of_le, &[lr, pp, le_lr_pp]);
        let one = d.num(1);
        let mul_one = d.lemma(p_.mul_one, &[pp]);

        let doubled = d.add(diff, diff);
        let start = d.add(lr, doubled);

        // `L + (G + G) = (L + G) + G`.
        let lr_g = d.add(lr, diff);
        let step1 = d.add(lr_g, diff);
        let h1 = {
            let fwd = d.lemma(p_.add_assoc, &[lr, diff, diff]);
            d.symm(step1, start, fwd)
        };

        // `(L + G) + G = pp + G`.
        let step2 = d.add(pp, diff);
        let h2 = d.congr(lr_g, pp, add_cancel, &|d, t| d.add(t, diff));

        // `pp + G = G + pp`.
        let step3 = d.add(diff, pp);
        let h3 = d.lemma(p_.add_comm, &[pp, diff]);

        // `G + pp = G + pp*1`.
        let scaled = d.mul(pp, one);
        let target = d.add(diff, scaled);
        let h4 = {
            let back = d.symm(scaled, pp, mul_one);
            d.congr(pp, scaled, back, &|d, t| d.add(diff, t))
        };

        let (_end, proof) = d.chain(
            start,
            &[(step1, h1), (step2, h2), (step3, h3), (target, h4)],
        );
        proof
    };

    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, sign])
}

/// `Nat.leastResidue_sumRange_reconcile` — see this module's doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
fn declare_least_residue_sum_range_reconcile(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.least_residue_sum_range_reconcile, 3, &|d, v| {
        let (ap, a, m) = (v[0], v[1], v[2]);
        let pp = d.succ(ap);

        // The five index functions, all one-based (`succ j`).
        let resid_fn = shifted(d, &|d, k| least_residue(d, &p, pp, a, k));
        let fold_fn = shifted(d, &|d, k| gauss_fold(d, &p, pp, a, k));
        let sign_fn = shifted(d, &|d, k| gauss_sign_neg(d, &p, pp, a, k));
        let sel_fn = shifted(d, &|d, k| {
            let sign = gauss_sign_neg(d, &p, pp, a, k);
            let fold = gauss_fold(d, &p, pp, a, k);
            let zero = d.zero();
            d.bool_select_nat(sign, fold, zero)
        });
        let ind_fn = shifted(d, &|d, k| {
            let sign = gauss_sign_neg(d, &p, pp, a, k);
            let one = d.num(1);
            let zero = d.zero();
            d.bool_select_nat(sign, one, zero)
        });

        // `fun j => sel j + sel j`, `fun j => pp * ind j`, and the two
        // combined summands the pointwise identity relates.
        let doubled_fn = shifted(d, &|d, k| {
            let sign = gauss_sign_neg(d, &p, pp, a, k);
            let fold = gauss_fold(d, &p, pp, a, k);
            let zero_a = d.zero();
            let sel_a = d.bool_select_nat(sign, fold, zero_a);
            let zero_b = d.zero();
            let sel_b = d.bool_select_nat(sign, fold, zero_b);
            d.add(sel_a, sel_b)
        });
        let scaled_fn = shifted(d, &|d, k| {
            let sign = gauss_sign_neg(d, &p, pp, a, k);
            let one = d.num(1);
            let zero = d.zero();
            let ind = d.bool_select_nat(sign, one, zero);
            d.mul(pp, ind)
        });
        let lhs_fn = shifted(d, &|d, k| {
            let lr = least_residue(d, &p, pp, a, k);
            let sign = gauss_sign_neg(d, &p, pp, a, k);
            let fold = gauss_fold(d, &p, pp, a, k);
            let zero_a = d.zero();
            let sel_a = d.bool_select_nat(sign, fold, zero_a);
            let zero_b = d.zero();
            let sel_b = d.bool_select_nat(sign, fold, zero_b);
            let doubled = d.add(sel_a, sel_b);
            d.add(lr, doubled)
        });
        let rhs_fn = shifted(d, &|d, k| {
            let fold = gauss_fold(d, &p, pp, a, k);
            let sign = gauss_sign_neg(d, &p, pp, a, k);
            let one = d.num(1);
            let zero = d.zero();
            let ind = d.bool_select_nat(sign, one, zero);
            let scaled = d.mul(pp, ind);
            d.add(fold, scaled)
        });

        let sum_resid = d.sum_range(resid_fn, m);
        let sum_fold = d.sum_range(fold_fn, m);
        let sum_sel = d.sum_range(sel_fn, m);
        let sum_ind = d.sum_range(ind_fn, m);
        let sum_doubled = d.sum_range(doubled_fn, m);
        let sum_scaled = d.sum_range(scaled_fn, m);
        let sum_lhs = d.sum_range(lhs_fn, m);
        let sum_rhs = d.sum_range(rhs_fn, m);

        // The pointwise identity, quantified over the index.
        let pointwise_all = {
            let nat = d.nat_ty();
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let body = pointwise(d, &p, ap, a, sj);
            d.lam_fv(j_fv, nat, body)
        };

        // ---- the chain ----------------------------------------------------
        let start = {
            let inner = d.add(sum_sel, sum_sel);
            d.add(sum_resid, inner)
        };

        // `sumRange (fun j => sel j + sel j) m = SIF + SIF`.
        let e1 = d.lemma(p.sum_range_add, &[sel_fn, sel_fn, m]);
        let step1 = d.add(sum_resid, sum_doubled);
        let h1 = {
            let doubled_pair = d.add(sum_sel, sum_sel);
            let back = d.symm(sum_doubled, doubled_pair, e1);
            d.congr(doubled_pair, sum_doubled, back, &|d, t| d.add(sum_resid, t))
        };

        // `sumRange lhs_fn m = sumRange resid m + sumRange doubled m`.
        let e2 = d.lemma(p.sum_range_add, &[resid_fn, doubled_fn, m]);
        let h2 = d.symm(sum_lhs, step1, e2);

        // The pointwise identity, lifted.
        let h3 = d.lemma(p.sum_range_congr, &[lhs_fn, rhs_fn, m, pointwise_all]);

        // `sumRange rhs_fn m = sumRange fold m + sumRange scaled m`.
        let step4 = d.add(sum_fold, sum_scaled);
        let h4 = d.lemma(p.sum_range_add, &[fold_fn, scaled_fn, m]);

        // `sumRange scaled m = pp * sumRange ind m`.
        let mul_pulled = d.mul(pp, sum_ind);
        let step5 = d.add(sum_fold, mul_pulled);
        let h5 = {
            let e5 = d.lemma(p.mul_sum_range, &[pp, ind_fn, m]);
            let back = d.symm(mul_pulled, sum_scaled, e5);
            d.congr(sum_scaled, mul_pulled, back, &|d, t| d.add(sum_fold, t))
        };

        // `sumRange ind m = countRange sign m` -- and that IS
        // `gaussNegCount pp a m` by delta, with no bridging step.
        let count = d.const_app(p.count_range, &[sign_fn, m]);
        let target = {
            let scaled = d.mul(pp, count);
            d.add(sum_fold, scaled)
        };
        let h6 = {
            let e6 = d.lemma(p.count_range_eq_sum_range, &[sign_fn, m]);
            let back = d.symm(count, sum_ind, e6);
            d.congr(sum_ind, count, back, &|d, t| {
                let scaled = d.mul(pp, t);
                d.add(sum_fold, scaled)
            })
        };

        let (_end, proof) = d.chain(
            start,
            &[
                (step1, h1),
                (sum_lhs, h2),
                (sum_rhs, h3),
                (step4, h4),
                (step5, h5),
                (target, h6),
            ],
        );

        // The STATEMENT is spelled with `Nat.sumRangeIf` and
        // `Nat.gaussNegCount`, both of which the chain's endpoints reach only
        // by delta -- that is deliberate: the consumer reads the named
        // aggregates, the proof works in the unfolded ones.
        let sif = d.const_app(p.sum_range_if, &[sign_fn, fold_fn, m]);
        let stmt = {
            let inner = d.add(sif, sif);
            let lhs = d.add(sum_resid, inner);
            let cnt = gauss_neg_count(d, &p, pp, a, m);
            let scaled = d.mul(pp, cnt);
            let rhs = d.add(sum_fold, scaled);
            d.eq(lhs, rhs)
        };
        (stmt, proof)
    })?;

    Ok(())
}

/// Declare everything this module owns.
///
/// Must run after `subset_sum.rs` (`Nat.sumRangeIf`) and after
/// `gauss_lemma.rs` (`Nat.leastResidue`, `Nat.gaussSignNeg`,
/// `Nat.gaussFold`, `Nat.gaussNegCount`).
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_gauss_residue_reconcile_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_least_residue_sum_range_reconcile(d, p)?;
    Ok(())
}
