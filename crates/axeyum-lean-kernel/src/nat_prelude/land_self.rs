//! `Nat.land_self : ∀ x, Eq (land x x) x` — `F:ml430-nat-and-self-06a84ccc`
//! (Mathlib's `&&&` for `Nat` is our `Nat.land`, already reconciled by
//! `land_comm`/`land_assoc`'s mirrors).
//!
//! Unlike `rec_agreement.rs`'s `land_comm`/`land_assoc`, this needs no
//! DOUBLE-fuel bridge: `land x x := landAux x x x` already puts the SAME
//! value in the fuel slot, so a single fuel induction over one generalized
//! value argument (`land_aux_self_of_fuel`) is enough, in the same shape as
//! `land_aux_comm_of_fuel` but with the two value slots forced equal from
//! the start.

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps, cases_mod_two, cases_zero_succ};
use super::rec_agreement::{guarded, half_le_predecessor_of_succ};
use crate::KernelError;
use crate::expr::ExprId;

/// Prove `∀ fuel a, P fuel a` by induction on `fuel`, with the value
/// argument `a` generalized in the motive (`fun fuel => ∀ a, P fuel a`) —
/// the one-variable twin of `ops.rs`'s `agree_by_fuel_induction`, needed
/// because `land_aux_self_of_fuel`'s statement only ever has ONE value slot
/// to generalize, not two.
fn self_by_fuel_induction(
    d: &mut NatDev<'_>,
    statement: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
    base: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    step: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
    fuel: ExprId,
) -> ExprId {
    let quantified = |d: &mut NatDev<'_>, at_fuel: ExprId| {
        let nat = d.nat_ty();
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let body = statement(d, at_fuel, a);
        d.pi_fv(a_fv, nat, body)
    };
    d.induct(
        &quantified,
        &|d| {
            let nat = d.nat_ty();
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let body = base(d, a);
            d.lam_fv(a_fv, nat, body)
        },
        &|d, predecessor, ih| {
            let nat = d.nat_ty();
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let body = step(d, predecessor, ih, a);
            d.lam_fv(a_fv, nat, body)
        },
        fuel,
    )
}

/// `land_aux_self_of_fuel : ∀ fuel a, Le a fuel → Eq (landAux fuel a a) a`.
///
/// Base (`fuel = 0`): `Le a 0` plus `zero_le a` forces `a = 0`
/// (`le_antisymm`); `landAux 0 a a` reduces to `0` regardless of `a`
/// (`refl`), which is then `a` by the derived equation.
///
/// Step (`fuel = succ k`, `ih : ∀ a, Le a k → Eq (landAux k a a) a`):
/// case-split `a`. `a = 0`: `landAux (succ k) 0 0` reduces to `0` directly
/// (the outer `n = 0` guard fires on the LITERAL `0`). `a = succ pa`: both
/// guards resolve to `false` (each checks a literal `succ`), landing on
/// `guarded(succ pa, succ pa, 0, 0, landAux k half half, mul bit bit)` where
/// `half := div (succ pa) 2`, `bit := mod (succ pa) 2`. `half_le
/// predecessor_of_succ` gives `Le half k` from the hypothesis, so the IH at
/// `half` gives `Eq (landAux k half half) half`; `bit * bit = bit` is one
/// `cases_mod_two` (`0*0=0`, `1*1=1`, both `refl`). What remains —
/// `2 * half + bit = succ pa` — is exactly `Nat.div_mod_exec`'s own
/// reconstruction equation at divisor `2`.
fn declare_land_aux_self_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId| {
        let bound = d.le(a, fuel);
        let lhs = d.const_app(p.land_aux, &[fuel, a, a]);
        let concl = d.eq(lhs, a);
        d.arrow(bound, concl)
    };

    let base = |d: &mut NatDev<'_>, a: ExprId| -> ExprId {
        let zero = d.zero();
        let bound_ty = d.le(a, zero);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);

        let zero_le_a = d.lemma(p.zero_le, &[a]);
        let a_eq_zero = d.lemma(p.le_antisymm, &[a, zero, h1, zero_le_a]);
        let zero_eq_a = d.symm(a, zero, a_eq_zero);

        let left_term = d.const_app(p.land_aux, &[zero, a, a]);
        let left_is_zero = d.refl(left_term); // Eq left_term zero, bridged by defeq
        let body = d.trans(left_term, zero, a, left_is_zero, zero_eq_a);
        d.lam_fv(h1_fv, bound_ty, body)
    };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId| -> ExprId {
        let sk = d.succ(k);
        cases_zero_succ(
            d,
            a,
            &|d, candidate| {
                let bound = d.le(candidate, sk);
                let lhs = d.const_app(p.land_aux, &[sk, candidate, candidate]);
                let concl = d.eq(lhs, candidate);
                d.arrow(bound, concl)
            },
            &|d| {
                let zero = d.zero();
                let bound_ty = d.le(zero, sk);
                let h_fv = d.fresh_fvar();
                let lhs = d.const_app(p.land_aux, &[sk, zero, zero]);
                let body = d.refl(lhs); // Eq lhs zero, bridged by defeq
                d.lam_fv(h_fv, bound_ty, body)
            },
            &|d, pa| {
                let e = d.succ(pa);
                let bound_ty = d.le(e, sk);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);

                let two = d.num(2);
                let zero = d.zero();
                let half = d.div(e, two);
                let bit = d.modulo(e, two);
                let rec = d.const_app(p.land_aux, &[k, half, half]);
                let bit_and = d.mul(bit, bit);

                // `Le half k` from `Le e sk` via the shared halving lemma.
                let half_le_k = half_le_predecessor_of_succ(d, &p, pa, k, h1);
                let ih_half = d.apply(ih, &[half]);
                let ih_half = d.apply(ih_half, &[half_le_k]); // Eq rec half

                // `bit * bit = bit`: `cases_mod_two` on `e`, both leaves `refl`.
                let bit_idem_at_zero = {
                    let z = d.zero();
                    let m0 = d.mul(z, z);
                    d.refl(m0)
                };
                let bit_idem_at_one = {
                    let one = d.num(1);
                    let m1 = d.mul(one, one);
                    d.refl(m1)
                };
                let bit_idem = cases_mod_two(
                    d,
                    &p,
                    e,
                    &|d, r| {
                        let m = d.mul(r, r);
                        d.eq(m, r)
                    },
                    bit_idem_at_zero,
                    bit_idem_at_one,
                );

                let start = guarded(d, e, e, zero, zero, rec, bit_and);
                let mid1 = guarded(d, e, e, zero, zero, half, bit_and);
                let step1 = d.congr(rec, half, ih_half, &|d, hole| {
                    guarded(d, e, e, zero, zero, hole, bit_and)
                });
                let mid2 = guarded(d, e, e, zero, zero, half, bit);
                let step2 = d.congr(bit_and, bit, bit_idem, &|d, hole| {
                    guarded(d, e, e, zero, zero, half, hole)
                });

                // `mid2` is defeq `add (mul two half) bit` -- the reconstruction
                // equation `div_mod_exec` proves at divisor `2`, value `e`.
                let one = d.num(1);
                let h_exec = d.lemma(p.div_mod_exec, &[one, e]);
                let mul_two_half = d.mul(two, half);
                let add_form = d.add(mul_two_half, bit);
                let left_ty = d.eq(e, add_form);
                let right_ty = d.lt(bit, two);
                let reconstruction = and_left(d, left_ty, right_ty, h_exec);
                let recon_rev = d.symm(e, add_form, reconstruction);
                let bridge = d.refl(mid2); // Eq mid2 add_form, bridged by defeq
                let mid2_to_e = d.trans(mid2, add_form, e, bridge, recon_rev);

                let step_ab = d.trans(start, mid1, mid2, step1, step2);
                let body = d.trans(start, mid2, e, step_ab, mid2_to_e);
                d.lam_fv(h1_fv, bound_ty, body)
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = self_by_fuel_induction(d, &statement, &base, &step, fuel);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let applied = d.apply(proof_fn, &[a]);
    let ty = {
        let body = statement(d, fuel, a);
        let with_a = d.pi_fv(a_fv, nat, body);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value = {
        let with_a = d.lam_fv(a_fv, nat, applied);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    d.declare_theorem(p.land_aux_self_of_fuel, ty, value)
}

/// `land_self : ∀ x, Eq (land x x) x` — `land_aux_self_of_fuel` at
/// `fuel := x`, `a := x` via `le_refl`; `land x x` and `landAux x x x` are
/// the same term by definition, so no further bridging is needed.
fn declare_land_self(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_self, 1, &|d, values| {
        let x = values[0];
        let le_refl_x = d.lemma(p.le_refl, &[x]);
        let proof = d.lemma(p.land_aux_self_of_fuel, &[x, x, le_refl_x]);
        let lhs = d.const_app(p.land, &[x, x]);
        (d.eq(lhs, x), proof)
    })?;
    Ok(())
}

/// Declare [`declare_land_aux_self_of_fuel`] and [`declare_land_self`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_self_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_land_aux_self_of_fuel(d, p)?;
    declare_land_self(d, p)?;
    Ok(())
}
