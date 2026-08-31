//! `Int.prodRangeIf_const_eq_pow_count : ∀ pred a n,
//! prodRangeIf pred (fun _ => a) n = pow a (countRange pred n)` -- item 3(a)
//! of the three-piece Fermat -> Euler handoff
//! (`docs/plan/status/374-euler-theorem.md`), the first slice of item 3
//! (`docs/plan/status/euler-theorem-spine.md` calls this the one piece of
//! the whole handoff that is genuinely new mathematics, "an induction this
//! kernel has not built before").
//!
//! A constant-`a` product restricted to `{k < n : pred k}` is `a` raised to
//! the count of that subset -- the multiplicative form of
//! `Nat.sumRange`-over-an-indicator being a count times a constant, and the
//! Euler-side analogue of `wilson.rs`'s `prod_range_const_one` (the
//! unrestricted `a := one` case, already proved there by the identical
//! induction shape).
//!
//! ## Proof: induction on `n`, following `prod_range_const_one`'s pattern
//!
//! Base (`n = 0`): both sides reduce to `one` by iota alone --
//! `prodRange _ 0 ≡ one`, `countRange pred 0 ≡ 0`, `pow a 0 ≡ one` -- no
//! lemma call, `Eq.refl`.
//!
//! Step (`n -> succ n`, `m := countRange pred n`, `c := pred n`): the goal is
//! `mul (prodRange sel n) (bool_select_int c a one) = pow a (add m
//! (bool_select_nat c 1 0))` (both `prodRange sel (succ n)` and
//! `countRange pred (succ n)` unfold to exactly this shape by iota, matching
//! `count_range_succ`'s own `Eq.refl` proof in `nat_prelude/totient.rs`).
//! `c` is symbolic (`pred` applied to a bound variable, not a literal
//! constructor), so this is NOT itself an iota redex -- it is closed by a
//! direct `Bool.rec` application at `c` (the same "supply a proof of the
//! goal at each LITERAL constructor, apply the recursor to the symbolic
//! value" idiom `nat_prelude/totient.rs`'s `count_step_le_one` and
//! `prod.rs`'s `ble_eq_false_of_lt` already use), giving:
//!
//! - `c = true`: `bool_select_int true a one ≡ a`,
//!   `bool_select_nat true 1 0 ≡ 1`, `add m 1 ≡ succ m` (`Nat.add` recurses
//!   on its RIGHT argument, so a literal-right `add _ (succ zero)` is two
//!   iota steps regardless of `m`'s shape), `pow a (succ m) ≡ mul (pow a m)
//!   a`. The goal reduces to `mul (prodRange sel n) a = mul (pow a m) a`,
//!   closed by `Int.congr` on the induction hypothesis.
//! - `c = false`: `bool_select_int false a one ≡ one`,
//!   `bool_select_nat false 1 0 ≡ 0`, `add m 0 ≡ m` (iota, right-argument
//!   base case). The goal reduces to `mul (prodRange sel n) one = pow a m`,
//!   closed by `Int.mul_one` chained with the induction hypothesis.
//!
//! No fact about which branch actually fires is needed in either case --
//! exactly `count_step_le_one`'s own comment on the same idiom.
//!
//! The statement is built in `prodRange`/`selector`-unfolded form, matching
//! `euler_theorem.rs`'s own convention (see that file's module doc): a
//! consumer applying the folded `Int.prodRangeIf` constant gets the same
//! fact by kernel-level delta unfolding at the point of use.

use super::ops::IntDev;
use super::prod::bool_select_int;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `fun k => natAbs`-style local copy of `euler_theorem.rs`'s private
/// `selector` (not `pub(super)` there, and this development's own
/// convention is per-file local copies over a shared private module --
/// see `nat_prelude/euler.rs`/`int_prelude/modinv.rs`'s doc comments on the
/// same choice): `fun i => bool_select_int (pred i) (f i) Int.one`.
fn selector(d: &mut IntDev<'_>, pred: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let pi = d.apply(pred, &[i]);
    let fi = d.apply(f, &[i]);
    let one = d.ione();
    let sel = bool_select_int(d, pi, fi, one);
    d.lam_fv(i_fv, nat, sel)
}

/// `Int.prodRangeIf_const_eq_pow_count : ∀ pred a n,
/// Eq Int (prodRange (selector pred (fun _ => a)) n) (pow a (countRange pred n))`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_if_const_eq_pow_count(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n_nat = d.kernel().fvar(n_fv);

    // `const_a := fun _:Nat => a`.
    let unused_fv = d.fresh_fvar();
    let const_a = d.lam_fv(unused_fv, nat, a);
    let sel = selector(d, pred, const_a);

    let lhs = d.const_app(p.prod_range, &[sel, n_nat]);
    let count_n = d.const_app(p.nat.count_range, &[pred, n_nat]);
    let rhs = d.ipow(a, count_n);
    let concl = d.ieq(lhs, rhs);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl);
        let with_a = d.pi_fv(a_fv, int_ty, with_n);
        d.pi_fv(pred_fv, pred_ty, with_a)
    };

    let induction_proof = {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let p = d.int();
            let pr = d.const_app(p.prod_range, &[sel, x]);
            let cnt = d.const_app(p.nat.count_range, &[pred, x]);
            let pw = d.ipow(a, cnt);
            d.ieq(pr, pw)
        };
        let base = &|d: &mut IntDev<'_>| -> ExprId {
            let one_i = d.ione();
            d.irefl(one_i)
        };
        let step = &|d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let p = d.int();
            let pr_j = d.const_app(p.prod_range, &[sel, j]);
            let cnt_j = d.const_app(p.nat.count_range, &[pred, j]);
            let pw_j = d.ipow(a, cnt_j);
            let cond = d.apply(pred, &[j]);
            let one_i = d.ione();

            // `motive_bool(x) := Eq Int (mul pr_j (bool_select_int x a one))
            //   (pow a (add cnt_j (bool_select_nat x 1 0)))`.
            let motive_bool = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let sel_val = bool_select_int(d, x, a, one_i);
                let lhs_b = d.imul(pr_j, sel_val);
                let one_nat = d.num(1);
                let zero_nat = d.zero();
                let inc = d.bool_select_nat(x, one_nat, zero_nat);
                let exp = d.add(cnt_j, inc);
                let rhs_b = d.ipow(a, exp);
                d.ieq(lhs_b, rhs_b)
            };

            let case_true = {
                // `c = true`: `pr_j * a = pow a (succ cnt_j) ≡ pow a cnt_j * a`.
                d.icongr(pr_j, pw_j, ih, &|d, t| d.imul(t, a))
            };
            let case_false = {
                // `c = false`: `pr_j * one = pr_j = pow a cnt_j`.
                let mul_one_lhs = d.imul(pr_j, one_i);
                let mul_one_pf = d.const_app(p.mul_one, &[pr_j]);
                let (_, chained) = d.ichain(mul_one_lhs, &[(pr_j, mul_one_pf), (pw_j, ih)]);
                chained
            };

            let motive_lam = {
                let x_fv = d.fresh_fvar();
                let x = d.kernel().fvar(x_fv);
                let body = motive_bool(d, x);
                let bool_ty = d.bool_ty();
                d.lam_fv(x_fv, bool_ty, body)
            };
            let level_zero = d.kernel().level_zero();
            let bool_rec = d.int().logic.bool_rec;
            let rec = d.kernel().const_(bool_rec, vec![level_zero]);
            d.apply(rec, &[motive_lam, case_false, case_true, cond])
        };
        d.induct(&motive, base, step, n_nat)
    };

    let value = {
        let with_n = d.lam_fv(n_fv, nat, induction_proof);
        let with_a = d.lam_fv(a_fv, int_ty, with_n);
        d.lam_fv(pred_fv, pred_ty, with_a)
    };

    d.declare_theorem(p.prod_range_if_const_eq_pow_count, ty, value)
}
