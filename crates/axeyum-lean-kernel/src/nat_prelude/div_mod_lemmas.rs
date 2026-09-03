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
//! remainder of `a+b` at `dd-1`, which this module's other machinery does not
//! reach. [`declare_add_div_of_dvd_add_add_one`] builds it directly: decompose
//! `a = c*qa+ra`, `b = c*qb+rb` (`div_mod_exec`), so `a+b+1 = c*(qa+qb) +
//! (ra+rb+1)`. Case-split `ra+rb+1` against `c` (`lt_or_ge`): below `c` this
//! is ALREADY a valid `divMod` decomposition of `a+b+1`, and comparing it
//! against the one the `dvd` witness gives (remainder `0`) via
//! `div_mod_unique` forces `ra+rb+1 = 0`, refuted by `succ_ne_zero` since it
//! is a successor. At or above `c`, subtracting `c` once (`sub_add_cancel`)
//! gives a remainder `r'` that is ALSO `< c` (bounded via `ra<c`, `rb<c` and
//! `le_of_succ_le_succ`/`add_le_add_left`/`add_le_add_right`/`le_trans`), so
//! `divMod c (a+b+1) (qa+qb+1) r'` is likewise valid; comparing it against the
//! same `dvd`-witness relation forces `r' = 0`, i.e. `ra+rb+1 = c` exactly.
//! That pins `ra+rb = c-1 < c`, so `(qa+qb, ra+rb)` is a valid `divMod`
//! decomposition of `a+b` itself, and comparing it against `div_mod_exec`'s
//! own decomposition of `a+b` via `div_mod_unique` one more time gives the
//! goal directly: `(a+b)/c = qa+qb`.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, cases_zero_succ};
use super::steps::absurd;
use super::steps::dvd_elim;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// Reconstruct `divMod dd x (div x dd) (mod x dd)` for any `x`, given
/// `pos_dd : Lt zero dd`. A local copy of `group.rs`'s private
/// `div_mod_reconstructed` -- see the module doc for why this is copied
/// rather than shared.
pub(super) fn div_mod_reconstructed(
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

/// `(a+b)+(c+d) = (a+c)+(b+d)`, returned as `Eq (add(add a b)(add c d))
/// (add(add a c)(add b d))`.
///
/// Retired to `crate::ring::nat` (docs/plan/status/460-ring-tactic-1.md): a
/// pure ring-rearrangement chain, now searched for and emitted rather than
/// hand-assembled — one of eight verbatim-duplicated hand proofs of this
/// exact identity across `nat_prelude` (`binomial.rs`, `finite_set.rs`,
/// `fibonacci.rs`, `subset_sum.rs`, `rec_agreement.rs`,
/// `count_range_reversal.rs`, `eisenstein_lemma.rs`).
fn add_add_add_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> (ExprId, ExprId) {
    let ac = d.add(a, c);
    let bd = d.add(b, dd);
    let target = d.add(ac, bd);
    // Generic-then-apply (`prove_eq_at`): this file's own callers pass
    // `div`/`mod` expressions for `a`/`b`/`c`, which `prove_eq` on the
    // literal terms would (correctly) decline `NonRing` on.
    let proof = crate::ring::nat::prove_eq_at(d, p, &[a, b, c, dd], &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let ab = d.add(a, b);
        let cd = d.add(c, dd);
        let lhs = d.add(ab, cd);
        let ac = d.add(a, c);
        let bd = d.add(b, dd);
        let rhs = d.add(ac, bd);
        (lhs, rhs)
    })
    .unwrap_or_else(|e| panic!("ring declined add_add_add_comm: {e:?}"));
    (target, proof)
}

/// `Nat.add_div_of_dvd_add_add_one : ∀ {c a b}, c ∣ (a+b+1) → (a+b)/c =
/// a/c + b/c`. See the module doc for the route.
///
/// Must run after `declare_euclidean_division` (`div_mod_unique`),
/// `declare_divisibility` (`div_mod_exec` via `declare_executable_division_spec`),
/// `declare_order`/`declare_order_more` (`lt_or_ge`, `sub_add_cancel`,
/// `le_of_succ_le_succ`, `le_succ_succ`, `add_le_add_left`/`_right`,
/// `le_trans`), and `declare_additive_theorems`/`declare_multiplicative_theorems`
/// (`add_assoc`, `add_comm`, `succ_injective`, `left_distrib`, `zero_add`).
///
/// # Errors
///
/// Returns the kernel's rejection if a generated declaration does not
/// type-check or a name is already taken.
pub(super) fn declare_add_div_of_dvd_add_add_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.add_div_of_dvd_add_add_one, 3, &|d, v| {
        let (c_outer, a, b) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let ab = d.add(a, b);
        let ab1 = d.add(ab, one);

        // motive(cc) : dvd cc ab1 -> (ab/cc) = (a/cc)+(b/cc)
        let motive = |d: &mut NatDev<'_>, cc: ExprId| -> ExprId {
            let dvd_ty = d.dvd(cc, ab1);
            let ab_div_cc = d.div(ab, cc);
            let a_div_cc = d.div(a, cc);
            let b_div_cc = d.div(b, cc);
            let rhs = d.add(a_div_cc, b_div_cc);
            let concl = d.eq(ab_div_cc, rhs);
            d.arrow(dvd_ty, concl)
        };

        // c = 0: dvd 0 ab1 gives ab1 = 0*q = 0, contradicting ab1 = succ(ab).
        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let dvd_ty = d.dvd(zero, ab1);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let ab_div_z = d.div(ab, zero);
            let a_div_z = d.div(a, zero);
            let b_div_z = d.div(b, zero);
            let sum_z = d.add(a_div_z, b_div_z);
            let goal = d.eq(ab_div_z, sum_z);
            let body = dvd_elim(d, zero, ab1, goal, hyp, &|d, q, eq_proof| {
                // eq_proof : Eq ab1 (mul zero q)
                let zero_mul_q = d.lemma(p.zero_mul, &[q]); // Eq (mul zero q) zero
                let zero = d.zero();
                let mul_zero_q = d.mul(zero, q);
                let (_, ab1_eq_zero) = d.chain(ab1, &[(mul_zero_q, eq_proof), (zero, zero_mul_q)]);
                let ne = d.lemma(p.succ_ne_zero, &[ab]);
                let false_val = d.apply(ne, &[ab1_eq_zero]);
                absurd(d, goal, false_val)
            });
            d.lam_fv(hyp_fv, dvd_ty, body)
        };

        // c = succ cpred: the main route, described in the module doc.
        let at_succ = |d: &mut NatDev<'_>, cpred: ExprId| -> ExprId {
            let c = d.succ(cpred);
            let dvd_ty = d.dvd(c, ab1);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            // Decompose a and b at divisor c.
            let exec_a = d.lemma(p.div_mod_exec, &[cpred, a]);
            let a_div_c = d.div(a, c);
            let ra = d.modulo(a, c);
            let mul_c_a = d.mul(c, a_div_c);
            let mul_c_a_ra = d.add(mul_c_a, ra);
            let eq_a_ty = d.eq(a, mul_c_a_ra);
            let bound_a_ty = d.lt(ra, c);
            let eq_a = and_left(d, eq_a_ty, bound_a_ty, exec_a);
            let bound_a = and_right(d, eq_a_ty, bound_a_ty, exec_a);

            let exec_b = d.lemma(p.div_mod_exec, &[cpred, b]);
            let b_div_c = d.div(b, c);
            let rb = d.modulo(b, c);
            let mul_c_b = d.mul(c, b_div_c);
            let mul_c_b_rb = d.add(mul_c_b, rb);
            let eq_b_ty = d.eq(b, mul_c_b_rb);
            let bound_b_ty = d.lt(rb, c);
            let eq_b = and_left(d, eq_b_ty, bound_b_ty, exec_b);
            let bound_b = and_right(d, eq_b_ty, bound_b_ty, exec_b);

            let qsum = d.add(a_div_c, b_div_c);
            let x_term = d.mul(c, qsum); // c*(a/c+b/c)
            let ra_rb = d.add(ra, rb);
            let final_target = d.add(x_term, ra_rb); // c*(a/c+b/c) + (ra+rb)

            // ab = (c*a_div_c+ra) + (c*b_div_c+rb)
            let mid1 = d.add(mul_c_a_ra, b);
            let step1 = d.congr(a, mul_c_a_ra, eq_a, &|d, v| d.add(v, b));
            let mid2 = d.add(mul_c_a_ra, mul_c_b_rb);
            let step2 = d.congr(b, mul_c_b_rb, eq_b, &|d, v| d.add(mul_c_a_ra, v));
            let (comm_target, comm_proof) = add_add_add_comm(d, &p, mul_c_a, ra, mul_c_b, rb);

            let distrib = d.lemma(p.left_distrib, &[c, a_div_c, b_div_c]); // x_term = mul_c_a+mul_c_b
            let sum_mul = d.add(mul_c_a, mul_c_b);
            let symm_distrib = d.symm(x_term, sum_mul, distrib);
            let distrib_step = d.congr(sum_mul, x_term, symm_distrib, &|d, v| d.add(v, ra_rb));

            let (_, ab_eq2) = d.chain(
                ab,
                &[
                    (mid1, step1),
                    (mid2, step2),
                    (comm_target, comm_proof),
                    (final_target, distrib_step),
                ],
            );

            // ab1 = ab+1 = c*(a_div_c+b_div_c) + (ra+rb+1)
            let rr1 = d.add(ra_rb, one);
            let mid3 = d.add(final_target, one);
            let step_ab1 = d.congr(ab, final_target, ab_eq2, &|d, v| d.add(v, one));
            let x_rr1 = d.add(x_term, rr1);
            let assoc_step = d.lemma(p.add_assoc, &[x_term, ra_rb, one]);
            let (_, ab1_eq2) = d.chain(ab1, &[(mid3, step_ab1), (x_rr1, assoc_step)]);

            let ab_div_c = d.div(ab, c);
            let goal = d.eq(ab_div_c, qsum);

            let body = dvd_elim(d, c, ab1, goal, hyp, &|d, q, eq_q| {
                let zero = d.zero();
                let zero_lt_c = d.lemma(p.zero_lt_succ, &[cpred]); // Lt zero c
                let mul_c_q = d.mul(c, q);
                let mul_c_q_zero = d.add(mul_c_q, zero);
                let padded_ty = d.eq(ab1, mul_c_q_zero);
                let zero_lt_c_ty = d.lt(zero, c);
                let divmod_from_dvd = d.const_app(
                    p.logic.and_intro,
                    &[padded_ty, zero_lt_c_ty, eq_q, zero_lt_c],
                );

                let lt_ty = d.lt(rr1, c);
                let ge_ty = d.le(c, rr1);
                let dichotomy = d.lemma(p.lt_or_ge, &[rr1, c]); // Or (Lt rr1 c) (Le c rr1)

                // Case Lt rr1 c: (qsum, rr1) is already a valid divMod for
                // ab1. Comparing it against the dvd-witness relation forces
                // rr1 = 0, impossible since rr1 = succ(ra+rb).
                let minor_lt = {
                    let lt_fv = d.fresh_fvar();
                    let rr1_lt_c = d.kernel().fvar(lt_fv);
                    let ab1_eq2_ty = d.eq(ab1, x_rr1);
                    let manufactured1 =
                        d.const_app(p.logic.and_intro, &[ab1_eq2_ty, lt_ty, ab1_eq2, rr1_lt_c]);
                    let both = d.lemma(
                        p.div_mod_unique,
                        &[c, ab1, qsum, rr1, q, zero, manufactured1, divmod_from_dvd],
                    );
                    let q1_ty = d.eq(qsum, q);
                    let r1_ty = d.eq(rr1, zero);
                    let rr1_eq_zero = and_right(d, q1_ty, r1_ty, both);
                    let ne = d.lemma(p.succ_ne_zero, &[ra_rb]);
                    let false_val = d.apply(ne, &[rr1_eq_zero]);
                    let body = absurd(d, goal, false_val);
                    d.lam_fv(lt_fv, lt_ty, body)
                };

                // Case Le c rr1: subtract c once to get remainder r' < c,
                // compare the shifted decomposition against the same
                // dvd-witness relation to force r' = 0, i.e. rr1 = c exactly
                // -- which pins ra+rb = c-1 < c, giving the goal.
                let minor_ge = {
                    let ge_fv = d.fresh_fvar();
                    let c_le_rr1 = d.kernel().fvar(ge_fv);
                    let r_prime = d.sub(rr1, c);
                    let sac_eq = d.lemma(p.sub_add_cancel, &[c, rr1, c_le_rr1]); // Eq (add r' c) rr1

                    let ra_le_cpred = d.lemma(p.le_of_succ_le_succ, &[ra, cpred, bound_a]);
                    let rb_le_cpred = d.lemma(p.le_of_succ_le_succ, &[rb, cpred, bound_b]);
                    let step_a = d.lemma(p.add_le_add_right, &[rb, ra, cpred, ra_le_cpred]);
                    let step_b = d.lemma(p.add_le_add_left, &[cpred, rb, cpred, rb_le_cpred]);
                    let cpred_cpred = d.add(cpred, cpred);
                    let cpred_rb = d.add(cpred, rb);
                    let combined =
                        d.lemma(p.le_trans, &[ra_rb, cpred_rb, cpred_cpred, step_a, step_b]);

                    // sac_eq, up to defeq (add r' c ≡ succ(add r' cpred);
                    // rr1 ≡ succ ra_rb), types as Eq(succ(add r' cpred))(succ ra_rb).
                    let r_prime_cpred = d.add(r_prime, cpred);
                    let r_cpred_eq_rarb =
                        d.lemma(p.succ_injective, &[r_prime_cpred, ra_rb, sac_eq]);
                    let symm_r_cpred = d.symm(r_prime_cpred, ra_rb, r_cpred_eq_rarb);
                    let combined_motive = d.eq_motive(ra_rb, &|d, x| d.le(x, cpred_cpred));
                    let combined2 = d.transport(
                        ra_rb,
                        combined_motive,
                        combined,
                        r_prime_cpred,
                        symm_r_cpred,
                    );
                    let final_le = d.lemma(
                        p.le_of_add_le_add_right,
                        &[cpred, r_prime, cpred, combined2],
                    );
                    let r_prime_lt_c = d.lemma(p.le_succ_succ, &[r_prime, cpred, final_le]); // Lt r' c

                    // eqfinal : Eq ab1 (add (add x_term c) r')
                    let r_prime_c = d.add(r_prime, c);
                    let rr1_eq_r_prime_c = d.symm(r_prime_c, rr1, sac_eq);
                    let step_a2 =
                        d.congr(rr1, r_prime_c, rr1_eq_r_prime_c, &|d, v| d.add(x_term, v));
                    let comm_rc = d.lemma(p.add_comm, &[r_prime, c]);
                    let c_r_prime = d.add(c, r_prime);
                    let step_b2 = d.congr(r_prime_c, c_r_prime, comm_rc, &|d, v| d.add(x_term, v));
                    let assoc2 = d.lemma(p.add_assoc, &[x_term, c, r_prime]);
                    let x_term_c = d.add(x_term, c);
                    let final_shape = d.add(x_term_c, r_prime);
                    let x_c_r_prime = d.add(x_term, c_r_prime);
                    let step_c2 = d.symm(final_shape, x_c_r_prime, assoc2);
                    let x_term_r_prime_c = d.add(x_term, r_prime_c);
                    let (_, eqfinal) = d.chain(
                        ab1,
                        &[
                            (x_rr1, ab1_eq2),
                            (x_term_r_prime_c, step_a2),
                            (x_c_r_prime, step_b2),
                            (final_shape, step_c2),
                        ],
                    );

                    let succ_qsum = d.succ(qsum);
                    let mul_c_succ_qsum = d.mul(c, succ_qsum);
                    let eq_ty2_rhs = d.add(mul_c_succ_qsum, r_prime);
                    let eq_ty2 = d.eq(ab1, eq_ty2_rhs);
                    let r_lt_c_ty = d.lt(r_prime, c);
                    let manufactured2 = d.const_app(
                        p.logic.and_intro,
                        &[eq_ty2, r_lt_c_ty, eqfinal, r_prime_lt_c],
                    );
                    let both2 = d.lemma(
                        p.div_mod_unique,
                        &[
                            c,
                            ab1,
                            succ_qsum,
                            r_prime,
                            q,
                            zero,
                            manufactured2,
                            divmod_from_dvd,
                        ],
                    );
                    let bq2_ty = d.eq(succ_qsum, q);
                    let br2_ty = d.eq(r_prime, zero);
                    let r_prime_eq_zero = and_right(d, bq2_ty, br2_ty, both2);

                    // c = rr1, via r' + c = rr1 and r' = 0.
                    let congr_rprime = d.congr(r_prime, zero, r_prime_eq_zero, &|d, v| d.add(v, c));
                    let zero_c = d.add(zero, c);
                    // congr_rprime : Eq (add r_prime c) (add zero c) = Eq r_prime_c zero_c
                    let symm_congr = d.symm(r_prime_c, zero_c, congr_rprime);
                    let (_, zero_c_eq_rr1) =
                        d.chain(zero_c, &[(r_prime_c, symm_congr), (rr1, sac_eq)]);
                    let zero_add_c = d.lemma(p.zero_add, &[c]); // Eq (add zero c) c
                    let symm_zero_add_c = d.symm(zero_c, c, zero_add_c);
                    let c_eq_rr1 = d.trans(c, zero_c, rr1, symm_zero_add_c, zero_c_eq_rr1);

                    // c = succ cpred, rr1 ≡ succ ra_rb (defeq): cancel.
                    let cpred_eq_rarb = d.lemma(p.succ_injective, &[cpred, ra_rb, c_eq_rr1]);
                    let lt_succ_self_cpred = d.lemma(p.lt_succ_self, &[cpred]); // Lt cpred c
                    let ra_rb_motive = d.eq_motive(cpred, &|d, x| d.lt(x, c));
                    let ra_rb_lt_c = d.transport(
                        cpred,
                        ra_rb_motive,
                        lt_succ_self_cpred,
                        ra_rb,
                        cpred_eq_rarb,
                    );

                    let ab_eq2_ty = d.eq(ab, final_target);
                    let ra_rb_lt_c_ty = d.lt(ra_rb, c);
                    let manufactured3 = d.const_app(
                        p.logic.and_intro,
                        &[ab_eq2_ty, ra_rb_lt_c_ty, ab_eq2, ra_rb_lt_c],
                    );
                    let exec_ab = d.lemma(p.div_mod_exec, &[cpred, ab]);
                    let ab_mod_c = d.modulo(ab, c);
                    let both3 = d.lemma(
                        p.div_mod_unique,
                        &[
                            c,
                            ab,
                            qsum,
                            ra_rb,
                            ab_div_c,
                            ab_mod_c,
                            manufactured3,
                            exec_ab,
                        ],
                    );
                    let q3_ty = d.eq(qsum, ab_div_c);
                    let r3_ty = d.eq(ra_rb, ab_mod_c);
                    let qsum_eq_divabc = and_left(d, q3_ty, r3_ty, both3);
                    let body = d.symm(qsum, ab_div_c, qsum_eq_divabc);
                    d.lam_fv(ge_fv, ge_ty, body)
                };

                let anon = d.anon_name();
                let or_ty = d.const_app(p.logic.or, &[lt_ty, ge_ty]);
                let goal_motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                d.apply(
                    or_rec,
                    &[lt_ty, ge_ty, goal_motive, minor_lt, minor_ge, dichotomy],
                )
            });
            d.lam_fv(hyp_fv, dvd_ty, body)
        };

        let stmt = motive(d, c_outer);
        let proof = cases_zero_succ(d, c_outer, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.div_mod_block : ∀ n a b, Lt b n →
///   And (Eq (div (add (mul n a) b) n) a) (Eq (mod (add (mul n a) b) n) b)`
///
/// The block decomposition read back: an index written as `n*a + b` with the
/// remainder `b` already known to be below `n` has quotient `a` and remainder
/// `b`, on the nose. Both halves at once, because they come from one
/// `Nat.div_mod_unique` and splitting them would duplicate the whole
/// derivation.
///
/// This is the bridge `Nat.countRange_product`'s consumer needs: that lemma's
/// two per-block hypotheses are stated at the index `add (mul n a) b`, and a
/// predicate written in terms of `div y n` and `mod y n` reduces there only
/// once these two equations are in hand.
///
/// One line of content. `divMod d n q r` is `n = d*q + r ∧ r < d`, so
/// `divMod n (n*a + b) a b` is `And (Eq.refl _) hb` — the hand-built witness
/// costs nothing — and `div_mod_unique` against
/// [`div_mod_reconstructed`]'s executable witness returns exactly the pair.
/// `Lt 0 n` comes from `Lt b n` through `Le 1 (succ b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_div_mod_block(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.div_mod_block, 3, &|d, values| {
        let n = values[0];
        let a = values[1];
        let b = values[2];

        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let hb_ty = d.lt(b, n);

        let na = d.mul(n, a);
        let value = d.add(na, b);
        let quotient = d.div(value, n);
        let remainder = d.modulo(value, n);
        let left_ty = d.eq(quotient, a);
        let right_ty = d.eq(remainder, b);
        let concl = d.const_app(p.logic.and, &[left_ty, right_ty]);

        // `Lt 0 n` from `Lt b n`: `Le 1 (succ b)` then transitivity.
        let zero = d.zero();
        let one = d.num(1);
        let zero_le_b = d.lemma(p.zero_le, &[b]);
        let succ_b = d.succ(b);
        let one_le_succ_b = d.lemma(p.succ_le_succ, &[zero, b, zero_le_b]);
        let pos_n = d.lemma(p.le_trans, &[one, succ_b, n, one_le_succ_b, hb]);

        let executable = div_mod_reconstructed(d, &p, n, pos_n, value);

        // `divMod n value a b` is `And (Eq value (add (mul n a) b)) (Lt b n)`,
        // and its left conjunct is `Eq.refl value` because `value` IS that sum.
        let eq_ty = d.eq(value, value);
        let refl_case = d.refl(value);
        let hand_built = d.const_app(p.logic.and_intro, &[eq_ty, hb_ty, refl_case, hb]);

        let pair = d.const_app(
            p.div_mod_unique,
            &[n, value, quotient, remainder, a, b, executable, hand_built],
        );

        let ty = d.arrow(hb_ty, concl);
        let proof = d.lam_fv(hb_fv, hb_ty, pair);
        (ty, proof)
    })?;
    Ok(())
}
