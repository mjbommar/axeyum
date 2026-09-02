//! **ADR-1540's residue 1: the additive Gauss bijection, instantiated.**
//!
//! ```text
//! Nat.gauss_fold_sumRange_eq : ∀ m a, Eq (gcd a (succ (mul 2 m))) 1 →
//!   Eq (sumRange (fun k => succ k) m)
//!      (sumRange (fun j => gaussFold (succ (mul 2 m)) a (succ j)) m)
//! ```
//!
//! `1 + 2 + … + m` equals `gaussFold pp a 1 + … + gaussFold pp a m` whenever
//! `a` is coprime to `pp = 2m+1`: the folded least residues are a permutation
//! of `[1, m]`, so summing them changes nothing.
//!
//! # Why this is assembly and not new mathematics
//!
//! Gauss's lemma has needed exactly this permutation since ADR-1130 and gets
//! it MULTIPLICATIVELY: `int_prelude/gauss_assembly.rs` runs
//! `Int.prodRange_permute` at the self-map
//! `σ j := pred (gaussFold pp a (succ j))` to prove `∏_{j<m} Φ_j = m!`. This
//! file is the same three steps with `Nat.sumRange_permute` (ADR-1540) in
//! place of the product:
//!
//! 1. `Nat.gauss_fold_shift_injective_on` and
//!    `Nat.gauss_fold_shift_maps_into` (`gauss_lemma.rs`, ADR-1015) supply
//!    `InjectiveOn σ m` and `MapsInto σ m` verbatim — they are already
//!    `Nat`-typed and quantified over exactly the predicates
//!    `sumRange_permute` takes, so there is no bridging step at all.
//! 2. `Nat.sumRange_permute` at `f := succ` gives
//!    `sumRange succ m = sumRange (fun k => succ (σ k)) m`.
//! 3. One `Nat.sumRange_congr_lt` repairs `succ (pred (gaussFold …))` to
//!    `gaussFold …`, by `Nat.succ_pred_of_pos` fed the positivity half of
//!    `Nat.gauss_fold_in_range`. That range lemma's third hypothesis is
//!    `Le k m` at `k := succ j`, which is `Lt j m` definitionally, so the
//!    congruence's own hypothesis is passed straight in.
//!
//! Nothing here is `Int`-valued and nothing is lifted: the whole statement
//! lives in `Nat`, which is what the floor-sum consumer
//! (`eisenstein_lattice.rs`) works in.
//!
//! # What this does NOT prove
//!
//! **Eisenstein's lemma is not proved.** This closes ADR-1540's residue 1
//! only. Residues 2 and 3 are untouched and are the reason the chain does not
//! continue here:
//!
//! - **The residue/fold reconciliation** wants
//!   `Σ leastResidue = Σ gaussFold + pp·N − 2·Σ_neg gaussFold`, i.e. a
//!   CONDITIONAL sum. `Nat.prodRangeIf` and `Int.prodRangeIf` exist; measured
//!   in this lane with `examples/shape_search --name-like sumRangeIf`, **no
//!   `sumRangeIf` exists in any prelude** (verdict `ABSENT`, against a
//!   `prodRangeIf` positive control returning 12 declarations). Nothing in
//!   this file builds one.
//! - **The mod-2 bookkeeping** over `Int.sumRange`/`Int.modEq_sumRange`
//!   likewise remains open.

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `sumRange f n`.
fn sum_range(d: &mut NatDev<'_>, f: ExprId, n: ExprId) -> ExprId {
    d.sum_range(f, n)
}

/// `fun k => f (g k)`.
fn compose(d: &mut NatDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let gk = d.apply(g, &[k]);
    let body = d.apply(f, &[gk]);
    d.lam_fv(k_fv, nat, body)
}

/// `Nat.gauss_fold_sumRange_eq` — see this module's doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_gauss_fold_sum_range_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.gauss_fold_sum_range_eq, 2, &|d, v| {
        let (m, a) = (v[0], v[1]);
        let nat = d.nat_ty();

        let one = d.num(1);
        let two = d.num(2);
        let mul2m = d.mul(two, m);
        let pp = d.succ(mul2m);

        let g = d.gcd(a, pp);
        let cop_ty = d.eq(g, one);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        // `σ j := pred (gaussFold pp a (succ j))`.
        let sigma = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let fold = d.const_app(p.gauss_fold, &[pp, a, sj]);
            let body = d.pred(fold);
            d.lam_fv(j_fv, nat, body)
        };
        // `f k := succ k`.
        let succ_fn = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.succ(k);
            d.lam_fv(k_fv, nat, body)
        };
        // `fun j => gaussFold pp a (succ j)`.
        let fold_fn = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let body = d.const_app(p.gauss_fold, &[pp, a, sj]);
            d.lam_fv(j_fv, nat, body)
        };

        let inj = d.lemma(p.gauss_fold_shift_injective_on, &[m, a, cop]);
        let maps = d.lemma(p.gauss_fold_shift_maps_into, &[m, a, cop]);
        let permute = d.lemma(p.sum_range_permute, &[succ_fn, sigma, m, inj, maps]);

        let composed = compose(d, succ_fn, sigma);
        let sum_succ = sum_range(d, succ_fn, m);
        let sum_composed = sum_range(d, composed, m);
        let sum_fold = sum_range(d, fold_fn, m);

        // `∀ j, Lt j m → Eq (succ (pred (gaussFold pp a (succ j))))
        //                   (gaussFold pp a (succ j))`.
        let pointwise = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, m);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);

            let sj = d.succ(j);
            let fold_sj = d.const_app(p.gauss_fold, &[pp, a, sj]);
            let zero = d.zero();
            let pos_ty = d.lt(zero, fold_sj);
            let le_ty = d.le(fold_sj, m);

            let pos_sj = d.zero_lt_succ(j);
            // `hj : Lt j m` is `Le (succ j) m` definitionally, which is the
            // range lemma's third hypothesis at `k := succ j`.
            let range = d.lemma(p.gauss_fold_in_range, &[m, a, sj, cop, pos_sj, hj]);
            let pos_fold = and_left(d, pos_ty, le_ty, range);

            let sp = d.lemma(p.succ_pred_of_pos, &[fold_sj, pos_fold]);
            let pred_fold = d.pred(fold_sj);
            let succ_pred = d.succ(pred_fold);
            let body = d.symm(fold_sj, succ_pred, sp);

            let with_hj = d.lam_fv(hj_fv, hj_ty, body);
            d.lam_fv(j_fv, nat, with_hj)
        };
        let repair = d.lemma(p.sum_range_congr_lt, &[composed, fold_fn, m, pointwise]);

        let (_end, body) = d.chain(sum_succ, &[(sum_composed, permute), (sum_fold, repair)]);

        let proof = d.lam_fv(cop_fv, cop_ty, body);
        let concl = d.eq(sum_succ, sum_fold);
        let stmt = d.arrow(cop_ty, concl);
        (stmt, proof)
    })?;

    Ok(())
}

/// Declare everything this module owns.
///
/// Must run after `Nat.sumRange_permute` (`sum_range_permute.rs`) and after
/// `Nat.gauss_fold_shift_injective_on`/`_maps_into`/`gauss_fold_in_range`
/// (`gauss_lemma.rs`).
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_gauss_fold_sum_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_gauss_fold_sum_range_eq(d, p)?;
    Ok(())
}
