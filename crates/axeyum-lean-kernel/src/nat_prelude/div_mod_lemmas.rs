//! The `ml430` `Nat` add/div/mod shift family: `add_div_left`, `add_div_right`,
//! `add_mod_left`, `add_mod_right`, `add_mul_div_left`, `add_mul_div_right`,
//! `add_mul_mod_self_left`, `add_mul_mod_self_right`.
//!
//! All eight reduce to one reusable fact: for a POSITIVE divisor `dd` and any
//! `n`, `k`, `(n + dd*k)/dd = n/dd + k` and `(n + dd*k)%dd = n%dd`
//! ([`div_mod_shift`]). The route is the standard one this prelude already
//! uses for division facts (`division.rs`'s `div_mod_exec`/`div_mod_unique`/
//! `div_mod_add_multiple`, reached via `succ_pred_of_pos` exactly as
//! `group.rs`'s private `div_mod_reconstructed` does — that helper is not
//! exported, so [`div_mod_reconstructed`] here is a small local copy, the
//! established per-file pattern for this helper (`fermat.rs`, `perfect.rs`,
//! `totient.rs` each carry their own `pos_implies_succ_pred` for the same
//! reason)):
//!
//!   1. `div_mod_exec` + `succ_pred_of_pos` reconstructs `divMod dd n (n/dd)
//!      (n%dd)` for any `x`, given `0 < dd` ([`div_mod_reconstructed`]).
//!   2. `div_mod_add_multiple` shifts that by `k` to `divMod dd (n+dd*k)
//!      (n/dd+k) (n%dd)`.
//!   3. A second `div_mod_reconstructed` at the dividend `n+dd*k` gives
//!      `divMod dd (n+dd*k) ((n+dd*k)/dd) ((n+dd*k)%dd)` directly.
//!   4. `div_mod_unique` on the two relations (same divisor, same dividend)
//!      forces the shifted quotient/remainder to equal the direct ones.
//!
//! `add_mul_div_left`/`add_mul_div_right` are `div_mod_shift`'s `div_eq`
//! directly (module `mul_comm` for the `_right` form, whose product is
//! `y*z` rather than `div_mod_add_multiple`'s `divisor*shift` order).
//! `add_mul_mod_self_left`/`_right` are the same for `mod_eq`, but carry NO
//! positivity hypothesis in the Mathlib statement, so each case-splits its
//! divisor via `cases_zero_succ`: at `0`, the product collapses via
//! `zero_mul`/`mul_zero` and `add_zero`, never touching division at all.
//! `add_div_left`/`add_div_right` are the `y = 1` (well, `k = 1`) instance of
//! `add_mul_div_left`/`_right` after an `add_comm`/`mul_one` bridge.
//!
//! `add_div_of_dvd_add_add_one` (the ninth mirror in this family) needs a
//! genuinely different argument -- the divisibility hypothesis pins the
//! remainder of `a+b` at `dd-1`, which this module's machinery does not
//! reach -- and is left open; see the handoff doc.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::KernelError;
use crate::expr::ExprId;

/// Reconstruct `divMod dd x (div x dd) (mod x dd)` for any `x`, given
/// `pos_dd : Lt zero dd`. A local copy of `group.rs`'s private
/// `div_mod_reconstructed` -- see the module doc for why this is copied
/// rather than shared.
fn div_mod_reconstructed(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dd: ExprId,
    pos_dd: ExprId,
    x: ExprId,
) -> ExprId {
    let p = *p;
    let succ_pred_witness = d.lemma(p.succ_pred_of_pos, &[dd]);
    let dd_eq_succ_pred = d.apply(succ_pred_witness, &[pos_dd]); // dd = succ (pred dd)
    let pred_dd = d.pred(dd);
    let succ_pred_dd = d.succ(pred_dd);
    let exec = d.lemma(p.div_mod_exec, &[pred_dd, x]); // divMod (succ pred_dd) x (div x (succ pred_dd)) (mod x (succ pred_dd))

    let motive = d.eq_motive(succ_pred_dd, &|d, y| {
        let q = d.div(x, y);
        let r = d.modulo(x, y);
        d.div_mod(y, x, q, r)
    });
    let eq_rev = d.symm(dd, succ_pred_dd, dd_eq_succ_pred); // succ_pred_dd = dd
    d.transport(succ_pred_dd, motive, exec, dd, eq_rev)
}

/// For `pos_dd : Lt zero dd`, return `(div_eq, mod_eq)` where
///   `div_eq : Eq (div (add n (mul dd k)) dd) (add (div n dd) k)`
///   `mod_eq : Eq (modulo (add n (mul dd k)) dd) (modulo n dd)`
///
/// i.e. `(n + dd*k)/dd = n/dd + k` and `(n + dd*k)%dd = n%dd`. See the module
/// doc for the four-step derivation.
fn div_mod_shift(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dd: ExprId,
    pos_dd: ExprId,
    n: ExprId,
    k: ExprId,
) -> (ExprId, ExprId) {
    let p = *p;
    let base = div_mod_reconstructed(d, &p, dd, pos_dd, n); // divMod dd n (n/dd) (n%dd)
    let nq = d.div(n, dd);
    let nr = d.modulo(n, dd);
    let product = d.mul(dd, k);
    let full = d.add(n, product); // n + dd*k
    let shifted = d.lemma(p.div_mod_add_multiple, &[dd, n, nq, nr, k, base]); // divMod dd full (nq+k) nr

    let direct = div_mod_reconstructed(d, &p, dd, pos_dd, full); // divMod dd full (full/dd) (full%dd)
    let fq = d.div(full, dd);
    let fr = d.modulo(full, dd);
    let shift_q = d.add(nq, k);

    let both = d.lemma(
        p.div_mod_unique,
        &[dd, full, shift_q, nr, fq, fr, shifted, direct],
    ); // And (shift_q = fq) (nr = fr)
    let q_eq_ty = d.eq(shift_q, fq);
    let r_eq_ty = d.eq(nr, fr);
    let q_eq = and_left(d, q_eq_ty, r_eq_ty, both); // shift_q = fq
    let r_eq = and_right(d, q_eq_ty, r_eq_ty, both); // nr = fr

    // `q_eq : Eq shift_q fq`, `r_eq : Eq nr fr` (that is what `and_left`/
    // `and_right` project from `both`, matching `q_eq_ty`/`r_eq_ty` above) --
    // `symm(a, b, h)` needs `h : Eq a b`, so the anchor order below is
    // `(shift_q, fq)`/`(nr, fr)`, NOT the reversed `(fq, shift_q)`/`(fr, nr)`
    // that a first draft of this file had, which built a `symm` whose motive
    // anchored at the wrong side and so was silently a no-op.
    let div_eq = d.symm(shift_q, fq, q_eq); // Eq fq shift_q, i.e. full/dd = n/dd+k
    let mod_eq = d.symm(nr, fr, r_eq); // Eq fr nr, i.e. full%dd = n%dd
    (div_eq, mod_eq)
}

/// Declare the eight `ml430` `Nat` add/div/mod shift mirrors that route
/// through [`div_mod_shift`]. Must run after `declare_euclidean_division`
/// (`div_mod_unique`, `div_mod_add_multiple`) and `declare_divisibility`
/// (which calls `declare_executable_division_spec`, giving `div_mod_exec`).
///
/// # Errors
///
/// Returns the kernel's rejection if a generated declaration does not
/// type-check or a name is already taken.
pub(super) fn declare_add_div_mod_shift_family(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // add_mul_div_left : ∀ x z {y}, 0 < y → (x + y*z)/y = x/y + z.
    // Product `y*z` is already `dd*k` with `dd := y`, `k := z` -- no `mul_comm`
    // bridge needed.
    d.theorem(p.add_mul_div_left, 3, &|d, v| {
        let (x, z, y) = (v[0], v[1], v[2]);
        let zero = d.zero();
        let pos_ty = d.lt(zero, y);
        let product = d.mul(y, z);
        let full = d.add(x, product);
        let lhs = d.div(full, y);
        let x_div_y = d.div(x, y);
        let rhs = d.add(x_div_y, z);
        let concl = d.eq(lhs, rhs);
        let stmt = d.arrow(pos_ty, concl);

        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);
        let (div_eq, _mod_eq) = div_mod_shift(d, &p, y, pos, x, z);
        let proof = d.lam_fv(pos_fv, pos_ty, div_eq);
        (stmt, proof)
    })?;

    // add_mul_div_right : ∀ x y {z}, 0 < z → (x + y*z)/z = x/z + y.
    // Product `y*z` needs `mul_comm` to become `dd*k` with `dd := z`, `k := y`.
    d.theorem(p.add_mul_div_right, 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let zero = d.zero();
        let pos_ty = d.lt(zero, z);
        let yz = d.mul(y, z);
        let full_yz = d.add(x, yz);
        let lhs = d.div(full_yz, z);
        let x_div_z = d.div(x, z);
        let rhs = d.add(x_div_z, y);
        let concl = d.eq(lhs, rhs);
        let stmt = d.arrow(pos_ty, concl);

        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);

        let comm = d.lemma(p.mul_comm, &[y, z]); // y*z = z*y
        let zy = d.mul(z, y);
        let full_zy = d.add(x, zy);
        let bridge = d.congr(yz, zy, comm, &|d, v| d.add(x, v)); // (x+y*z) = (x+z*y)
        let bridge_div = d.congr(full_yz, full_zy, bridge, &|d, v| d.div(v, z));
        // bridge_div : (x+y*z)/z = (x+z*y)/z

        let (div_eq, _mod_eq) = div_mod_shift(d, &p, z, pos, x, y); // (x+z*y)/z = x/z+y
        let full_zy_div_z = d.div(full_zy, z);
        let (_, proof_body) = d.chain(lhs, &[(full_zy_div_z, bridge_div), (rhs, div_eq)]);
        let proof = d.lam_fv(pos_fv, pos_ty, proof_body);
        (stmt, proof)
    })?;

    // add_mul_mod_self_left : ∀ x y z, (x + y*z)%y = x%y. No positivity
    // hypothesis, so case-split on y.
    d.theorem(p.add_mul_mod_self_left, 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, yy: ExprId| -> ExprId {
            let product = d.mul(yy, z);
            let full = d.add(x, product);
            let lhs = d.modulo(full, yy);
            let rhs = d.modulo(x, yy);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, y);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let zero_mul_z = d.lemma(p.zero_mul, &[z]); // 0*z = 0
            let product = d.mul(zero, z);
            let sum = d.add(x, product);
            let step1 = d.congr(product, zero, zero_mul_z, &|d, v| d.add(x, v)); // x+0*z = x+0
            let add_zero_x = d.lemma(p.add_zero, &[x]); // x+0 = x
            let sum_zero = d.add(x, zero);
            let (_, combined) = d.chain(sum, &[(sum_zero, step1), (x, add_zero_x)]);
            d.congr(sum, x, combined, &|d, v| d.modulo(v, zero))
        };
        let at_succ = |d: &mut NatDev<'_>, ypred: ExprId| -> ExprId {
            let y = d.succ(ypred);
            let pos_y = d.lemma(p.zero_lt_succ, &[ypred]);
            let (_div_eq, mod_eq) = div_mod_shift(d, &p, y, pos_y, x, z);
            mod_eq
        };
        let proof = cases_zero_succ(d, y, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    // add_mul_mod_self_right : ∀ x y z, (x + y*z)%z = x%z. No positivity
    // hypothesis, so case-split on z; the positive branch needs `mul_comm`
    // (product is `y*z`, `div_mod_shift` wants `dd*k` with `dd := z`).
    d.theorem(p.add_mul_mod_self_right, 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, zz: ExprId| -> ExprId {
            let product = d.mul(y, zz);
            let full = d.add(x, product);
            let lhs = d.modulo(full, zz);
            let rhs = d.modulo(x, zz);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, z);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let mul_y_zero = d.lemma(p.mul_zero, &[y]); // y*0 = 0
            let product = d.mul(y, zero);
            let sum = d.add(x, product);
            let step1 = d.congr(product, zero, mul_y_zero, &|d, v| d.add(x, v)); // x+y*0 = x+0
            let add_zero_x = d.lemma(p.add_zero, &[x]); // x+0 = x
            let sum_zero = d.add(x, zero);
            let (_, combined) = d.chain(sum, &[(sum_zero, step1), (x, add_zero_x)]);
            d.congr(sum, x, combined, &|d, v| d.modulo(v, zero))
        };
        let at_succ = |d: &mut NatDev<'_>, zpred: ExprId| -> ExprId {
            let z = d.succ(zpred);
            let pos_z = d.lemma(p.zero_lt_succ, &[zpred]);
            let yz = d.mul(y, z);
            let full_yz = d.add(x, yz);

            let comm = d.lemma(p.mul_comm, &[y, z]); // y*z = z*y
            let zy = d.mul(z, y);
            let full_zy = d.add(x, zy);
            let bridge = d.congr(yz, zy, comm, &|d, v| d.add(x, v)); // (x+y*z) = (x+z*y)
            let bridge_mod = d.congr(full_yz, full_zy, bridge, &|d, v| d.modulo(v, z));
            // bridge_mod : (x+y*z)%z = (x+z*y)%z

            let (_div_eq, mod_eq) = div_mod_shift(d, &p, z, pos_z, x, y); // (x+z*y)%z = x%z
            let target_r = d.modulo(x, z);
            let full_yz_mod_z = d.modulo(full_yz, z);
            let full_zy_mod_z = d.modulo(full_zy, z);
            let (_, proof_body) = d.chain(
                full_yz_mod_z,
                &[(full_zy_mod_z, bridge_mod), (target_r, mod_eq)],
            );
            proof_body
        };
        let proof = cases_zero_succ(d, z, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    // add_mod_left : ∀ x z, (x + z)%x = z%x. No positivity hypothesis (`x` is
    // the divisor), so case-split on `x`; the positive branch reads `x+z` as
    // `z + x*1` (`add_comm` then `mul_one` backwards) to reach
    // `div_mod_shift`'s `n + dd*k` shape with `dd := x`, `n := z`, `k := 1`.
    d.theorem(p.add_mod_left, 2, &|d, v| {
        let (x, z) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, xx: ExprId| -> ExprId {
            let full = d.add(xx, z);
            let lhs = d.modulo(full, xx);
            let rhs = d.modulo(z, xx);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, x);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let zero_add_z = d.lemma(p.zero_add, &[z]); // 0+z = z
            let full = d.add(zero, z);
            d.congr(full, z, zero_add_z, &|d, v| d.modulo(v, zero))
        };
        let at_succ = |d: &mut NatDev<'_>, xpred: ExprId| -> ExprId {
            let x = d.succ(xpred);
            let pos_x = d.lemma(p.zero_lt_succ, &[xpred]);
            let full = d.add(x, z);

            let comm = d.lemma(p.add_comm, &[x, z]); // x+z = z+x
            let zx = d.add(z, x);
            let bridge1 = d.congr(full, zx, comm, &|d, v| d.modulo(v, x)); // (x+z)%x = (z+x)%x

            let mul_one_x = d.lemma(p.mul_one, &[x]); // x*1 = x
            let one = d.num(1);
            let x_mul_one = d.mul(x, one);
            let rev = d.symm(x_mul_one, x, mul_one_x); // x = x*1
            let z_plus_xmulone = d.add(z, x_mul_one);
            let bridge2 = d.congr(x, x_mul_one, rev, &|d, v| {
                let sum = d.add(z, v);
                d.modulo(sum, x)
            });
            // bridge2 : (z+x)%x = (z+x*1)%x

            let (_div_eq, mod_eq) = div_mod_shift(d, &p, x, pos_x, z, one); // (z+x*1)%x = z%x
            let target_r = d.modulo(z, x);
            let full_mod_x = d.modulo(full, x);
            let zx_mod_x = d.modulo(zx, x);
            let z_plus_xmulone_mod_x = d.modulo(z_plus_xmulone, x);
            let (_, proof_body) = d.chain(
                full_mod_x,
                &[
                    (zx_mod_x, bridge1),
                    (z_plus_xmulone_mod_x, bridge2),
                    (target_r, mod_eq),
                ],
            );
            proof_body
        };
        let proof = cases_zero_succ(d, x, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    // add_mod_right : ∀ x z, (x + z)%z = x%z. No positivity hypothesis;
    // case-split on `z`. Positive branch reads `x+z` as `x + z*1`
    // (`mul_one` backwards).
    d.theorem(p.add_mod_right, 2, &|d, v| {
        let (x, z) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, zz: ExprId| -> ExprId {
            let full = d.add(x, zz);
            let lhs = d.modulo(full, zz);
            let rhs = d.modulo(x, zz);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, z);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let add_zero_x = d.lemma(p.add_zero, &[x]); // x+0 = x
            let full = d.add(x, zero);
            d.congr(full, x, add_zero_x, &|d, v| d.modulo(v, zero))
        };
        let at_succ = |d: &mut NatDev<'_>, zpred: ExprId| -> ExprId {
            let z = d.succ(zpred);
            let pos_z = d.lemma(p.zero_lt_succ, &[zpred]);
            let full = d.add(x, z);

            let mul_one_z = d.lemma(p.mul_one, &[z]); // z*1 = z
            let one = d.num(1);
            let z_mul_one = d.mul(z, one);
            let rev = d.symm(z_mul_one, z, mul_one_z); // z = z*1
            let x_plus_zmulone = d.add(x, z_mul_one);
            let bridge = d.congr(z, z_mul_one, rev, &|d, v| {
                let sum = d.add(x, v);
                d.modulo(sum, z)
            });
            // bridge : (x+z)%z = (x+z*1)%z

            let (_div_eq, mod_eq) = div_mod_shift(d, &p, z, pos_z, x, one); // (x+z*1)%z = x%z
            let target_r = d.modulo(x, z);
            let full_mod_z = d.modulo(full, z);
            let x_plus_zmulone_mod_z = d.modulo(x_plus_zmulone, z);
            let (_, proof_body) = d.chain(
                full_mod_z,
                &[(x_plus_zmulone_mod_z, bridge), (target_r, mod_eq)],
            );
            proof_body
        };
        let proof = cases_zero_succ(d, z, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    // add_div_left : ∀ x {z}, 0 < z → (z+x)/z = x/z+1. The `y := 1` instance
    // of `add_mul_div_left`'s shape, reordered by `add_comm` then bridged by
    // `mul_one` backwards to reach `x + z*1`.
    d.theorem(p.add_div_left, 2, &|d, v| {
        let (x, z) = (v[0], v[1]);
        let zero = d.zero();
        let pos_ty = d.lt(zero, z);
        let full = d.add(z, x);
        let lhs = d.div(full, z);
        let one = d.num(1);
        let x_div_z = d.div(x, z);
        let rhs = d.add(x_div_z, one);
        let concl = d.eq(lhs, rhs);
        let stmt = d.arrow(pos_ty, concl);

        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);

        let comm = d.lemma(p.add_comm, &[z, x]); // z+x = x+z
        let xz = d.add(x, z);
        let bridge1 = d.congr(full, xz, comm, &|d, v| d.div(v, z)); // (z+x)/z = (x+z)/z

        let mul_one_z = d.lemma(p.mul_one, &[z]); // z*1 = z
        let z_mul_one = d.mul(z, one);
        let rev = d.symm(z_mul_one, z, mul_one_z); // z = z*1
        let x_plus_zmulone = d.add(x, z_mul_one);
        let bridge2 = d.congr(z, z_mul_one, rev, &|d, v| {
            let sum = d.add(x, v);
            d.div(sum, z)
        });
        // bridge2 : (x+z)/z = (x+z*1)/z

        let (div_eq, _mod_eq) = div_mod_shift(d, &p, z, pos, x, one); // (x+z*1)/z = x/z+1
        let xz_div_z = d.div(xz, z);
        let x_plus_zmulone_div_z = d.div(x_plus_zmulone, z);
        let (_, proof_body) = d.chain(
            lhs,
            &[
                (xz_div_z, bridge1),
                (x_plus_zmulone_div_z, bridge2),
                (rhs, div_eq),
            ],
        );
        let proof = d.lam_fv(pos_fv, pos_ty, proof_body);
        (stmt, proof)
    })?;

    // add_div_right : ∀ x {z}, 0 < z → (x+z)/z = x/z+1. Same as
    // `add_div_left` without the `add_comm` bridge.
    d.theorem(p.add_div_right, 2, &|d, v| {
        let (x, z) = (v[0], v[1]);
        let zero = d.zero();
        let pos_ty = d.lt(zero, z);
        let full = d.add(x, z);
        let lhs = d.div(full, z);
        let one = d.num(1);
        let x_div_z = d.div(x, z);
        let rhs = d.add(x_div_z, one);
        let concl = d.eq(lhs, rhs);
        let stmt = d.arrow(pos_ty, concl);

        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);

        let mul_one_z = d.lemma(p.mul_one, &[z]); // z*1 = z
        let z_mul_one = d.mul(z, one);
        let rev = d.symm(z_mul_one, z, mul_one_z); // z = z*1
        let x_plus_zmulone = d.add(x, z_mul_one);
        let bridge = d.congr(z, z_mul_one, rev, &|d, v| {
            let sum = d.add(x, v);
            d.div(sum, z)
        });
        // bridge : (x+z)/z = (x+z*1)/z

        let (div_eq, _mod_eq) = div_mod_shift(d, &p, z, pos, x, one); // (x+z*1)/z = x/z+1
        let x_plus_zmulone_div_z = d.div(x_plus_zmulone, z);
        let (_, proof_body) = d.chain(lhs, &[(x_plus_zmulone_div_z, bridge), (rhs, div_eq)]);
        let proof = d.lam_fv(pos_fv, pos_ty, proof_body);
        (stmt, proof)
    })?;

    Ok(())
}
