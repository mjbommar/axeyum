//! ℤ-layer transport of `nat_prelude/gcd_mul_right_mirrors.rs`'s three
//! `ml430` mirrors, across `Int.gcd`'s `natAbs` bridge (`gcd.rs`):
//!
//! - `Int.dvd_gcd_mul_iff_dvd_mul` (`F:ml430-int-dvd-gcd-mul-iff-dvd-mul-12f61b99`):
//!   `∀ {k n m : ℤ}, k ∣ ↑(k.gcd n) * m ↔ k ∣ n * m`.
//! - `Int.dvd_mul_gcd_iff_dvd_mul` (`F:ml430-int-dvd-mul-gcd-iff-dvd-mul-22d6488e`):
//!   `∀ {k n m : ℤ}, k ∣ n * ↑(k.gcd m) ↔ k ∣ n * m`.
//! - `Int.dvd_gcd_mul_gcd_iff_dvd_mul` (`F:ml430-int-dvd-gcd-mul-gcd-iff-dvd-mul-8ea752a5`):
//!   `∀ {k n m : ℤ}, k ∣ ↑(k.gcd n) * ↑(k.gcd m) ↔ k ∣ n * m`.
//!
//! `docs/plan/status/335-int-dvd-mirrors.md` left these three open, naming the
//! shared blocker: a `Nat`-level distributive law over `gcd`
//! (`Nat.gcd_mul_right`) that did not exist yet. `docs/plan/status/336-gcd-mul-right.md`
//! built it and closed the `Nat` mirrors (`nat_prelude/gcd_mul_right_mirrors.rs`).
//! This file is the transport, not a re-derivation: no new base algebra, no
//! new `Int.rec`/`Nat.rec` case split.
//!
//! # Why this is a transport
//!
//! `Int.gcd a b := Nat.gcd (natAbs a) (natAbs b)` (`gcd.rs`), and `Int.dvd` is
//! equivalent to `Nat.dvd` on magnitudes in both directions
//! (`nat_abs_dvd_nat_abs_of_dvd`/`dvd_of_nat_abs_dvd`, also `gcd.rs`). Taking
//! `natAbs` of a product is multiplicative (`nat_abs_mul`, `gcd.rs`), and
//! `natAbs (ofNat c) ≡ c` by `rfl` for `c : Nat` (`Int.natAbs`'s `ofNat`
//! branch), so the kernel bridges that gap on its own wherever a proof
//! passes `natAbs (ofNat c)` where `c` is expected, or vice versa — no
//! explicit lemma is built for it here.
//!
//! [`idvd_mul_iff_nat_dvd_mul`] packages exactly this:
//! `Iff (idvd k (x*y)) (Nat.dvd (natAbs k) (natAbs x * natAbs y))` for any
//! `k, x, y : Int`. [`int_dvd_gcd_scaled_iff`] specializes it at
//! `x := ofNat (k.gcd b)` to get `Iff (idvd k ((ofNat (k.gcd b))*c)) (idvd k
//! (b*c))`, chaining against the already-proved `Nat`-level
//! `dvd_gcd_mul_iff_dvd_mul` (`na_k`'s `Nat.gcd (natAbs k) (natAbs b)` unifies
//! with `k.gcd b` by `Int.gcd`'s own definition, again a bare delta-unfold the
//! kernel resolves at `add_declaration` time).
//!
//! `Int.dvd_gcd_mul_iff_dvd_mul` is [`int_dvd_gcd_scaled_iff`] directly, at
//! `(b, c) := (n, m)`. `Int.dvd_mul_gcd_iff_dvd_mul` needs the scaling factor
//! on the right, so it commutes both sides of the shape applied at
//! `(b, c) := (m, n)` into place (`Int.mul_comm`) — mirroring the `Nat` file's
//! `dvd_mul_gcd_iff_dvd_mul` exactly, one layer up. `Int.dvd_gcd_mul_gcd_iff_dvd_mul`
//! applies the shape at `c := ofNat (k.gcd m)` and chains one more `iff_trans`
//! against `dvd_mul_gcd_iff_dvd_mul`, for the same reason the `Nat` mirror
//! does — this is why `dvd_mul_gcd_iff_dvd_mul` must be declared first.

use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::IntPrelude;
use super::ops::IntDev;

// ---------------------------------------------------------------------------
// Small local term-building helpers (this development's convention: each
// file keeps its own thin copies rather than sharing them — see `dvd.rs`'s
// and `gcd.rs`'s module docs).
// ---------------------------------------------------------------------------

/// `Int.natAbs a`.
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().nat_abs;
    d.const_app(f, &[a])
}

/// `Int.gcd a b` (`Nat`-valued).
fn igcd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().gcd;
    d.const_app(f, &[a, b])
}

/// `h : Eq Nat a b  ⊢  Iff (pred a) (pred b)`, for an arbitrary `Nat -> Prop`.
/// `Eq.rec` at the reflexive instance. Local copy of
/// `nat_prelude/gcd_mul_right_mirrors.rs`'s combinator of the same name,
/// retyped for `IntDev` (its `NatOps` impl provides the same `transport`/
/// `eq_motive` this needs).
fn pred_iff_of_eq(
    d: &mut IntDev<'_>,
    p: &IntPrelude,
    a: ExprId,
    b: ExprId,
    eq_ab: ExprId,
    pred: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let pa = pred(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let px = pred(d, x);
        d.const_app(p.logic.iff, &[pa, px])
    });
    let refl_case = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let id = d.lam_fv(x_fv, pa, x);
        d.const_app(p.logic.iff_intro, &[pa, pa, id, id])
    };
    d.transport(a, motive, refl_case, b, eq_ab)
}

/// `h : Eq Int a b  ⊢  Iff (pred a) (pred b)`. The `Int`-typed twin of
/// [`pred_iff_of_eq`] (`Int.mul_comm`'s equations live at `Int`, not `Nat`).
fn pred_iff_of_eq_int(
    d: &mut IntDev<'_>,
    p: &IntPrelude,
    a: ExprId,
    b: ExprId,
    eq_ab: ExprId,
    pred: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let pa = pred(d, a);
    let motive = d.ieq_motive(a, &|d, x| {
        let px = pred(d, x);
        d.const_app(p.logic.iff, &[pa, px])
    });
    let refl_case = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let id = d.lam_fv(x_fv, pa, x);
        d.const_app(p.logic.iff_intro, &[pa, pa, id, id])
    };
    d.itransport(a, motive, refl_case, b, eq_ab)
}

/// `h1 : Iff A B, h2 : Iff B C  ⊢  Iff A C`. Local copy; works for an `Iff`
/// between any two `Prop`s regardless of which carrier they're about, since
/// `Iff`/`Iff.intro`/`Iff.mp`/`Iff.mpr` don't mention one.
fn iff_trans(
    d: &mut IntDev<'_>,
    p: &IntPrelude,
    a_ty: ExprId,
    b_ty: ExprId,
    c_ty: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = *p;
    let mp = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let h1_mp = d.const_app(p.logic.iff_mp, &[a_ty, b_ty, h1]);
        let b_from_a = d.apply(h1_mp, &[a]);
        let h2_mp = d.const_app(p.logic.iff_mp, &[b_ty, c_ty, h2]);
        let c_from_b = d.apply(h2_mp, &[b_from_a]);
        d.lam_fv(a_fv, a_ty, c_from_b)
    };
    let mpr = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let h2_mpr = d.const_app(p.logic.iff_mpr, &[b_ty, c_ty, h2]);
        let b_from_c = d.apply(h2_mpr, &[c]);
        let h1_mpr = d.const_app(p.logic.iff_mpr, &[a_ty, b_ty, h1]);
        let a_from_b = d.apply(h1_mpr, &[b_from_c]);
        d.lam_fv(c_fv, c_ty, a_from_b)
    };
    d.const_app(p.logic.iff_intro, &[a_ty, c_ty, mp, mpr])
}

/// `h : Iff A B  ⊢  Iff B A`. Local copy.
fn iff_symm(d: &mut IntDev<'_>, p: &IntPrelude, a_ty: ExprId, b_ty: ExprId, h: ExprId) -> ExprId {
    let p = *p;
    let mp = d.const_app(p.logic.iff_mpr, &[a_ty, b_ty, h]);
    let mpr = d.const_app(p.logic.iff_mp, &[a_ty, b_ty, h]);
    d.const_app(p.logic.iff_intro, &[b_ty, a_ty, mp, mpr])
}

// ---------------------------------------------------------------------------
// The shared shape.
// ---------------------------------------------------------------------------

/// `Iff (idvd k (imul x y)) (Nat.dvd (natAbs k) (Nat.mul (natAbs x) (natAbs y)))`,
/// for any `k, x, y : Int`. Combines the `natAbs`/`dvd` bridge
/// (`nat_abs_dvd_nat_abs_of_dvd`/`dvd_of_nat_abs_dvd`, `gcd.rs`) with
/// multiplicativity of `natAbs` (`nat_abs_mul`, `gcd.rs`). See the module doc.
fn idvd_mul_iff_nat_dvd_mul(
    d: &mut IntDev<'_>,
    p: &IntPrelude,
    k: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let p = *p;
    let xy = d.imul(x, y);
    let na_k = nat_abs(d, k);
    let na_x = nat_abs(d, x);
    let na_y = nat_abs(d, y);
    let na_xy = nat_abs(d, xy);
    let na_x_y = d.mul(na_x, na_y);

    let lhs = super::dvd::idvd(d, k, xy);
    let mid = d.dvd(na_k, na_xy);
    let rhs = d.dvd(na_k, na_x_y);

    let bridge = {
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[k, xy, h]);
            d.lam_fv(h_fv, lhs, body)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.const_app(p.dvd_of_nat_abs_dvd, &[k, xy, h]);
            d.lam_fv(h_fv, mid, body)
        };
        d.const_app(p.logic.iff_intro, &[lhs, mid, mp, mpr])
    };
    // bridge : Iff lhs mid

    let eq_xy = d.const_app(p.nat_abs_mul, &[x, y]); // Eq Nat na_xy na_x_y
    let transported = pred_iff_of_eq(d, &p, na_xy, na_x_y, eq_xy, &|d, v| d.dvd(na_k, v));
    // transported : Iff mid rhs

    iff_trans(d, &p, lhs, mid, rhs, bridge, transported)
}

/// `Iff (idvd k (imul (ofNat (igcd k b)) c)) (idvd k (imul b c))`, for any
/// `k, b, c : Int`. The shape behind all three facts — see the module doc.
fn int_dvd_gcd_scaled_iff(
    d: &mut IntDev<'_>,
    p: &IntPrelude,
    k: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let p = *p;
    let gkb = igcd(d, k, b);
    let of_gkb = d.of_nat(gkb);

    let left = idvd_mul_iff_nat_dvd_mul(d, &p, k, of_gkb, c);
    let right = idvd_mul_iff_nat_dvd_mul(d, &p, k, b, c);

    let na_k = nat_abs(d, k);
    let na_b = nat_abs(d, b);
    let na_c = nat_abs(d, c);

    // core : Iff (Nat.dvd na_k (Nat.gcd na_k na_b * na_c))
    //            (Nat.dvd na_k (na_b * na_c))
    // `Nat.gcd na_k na_b` unifies with `gkb` by `Int.gcd`'s own definition.
    let core = d.lemma(p.nat.dvd_gcd_mul_iff_dvd_mul, &[na_k, na_b, na_c]);

    let of_gkb_c = d.imul(of_gkb, c);
    let bc = d.imul(b, c);
    let lhs_a = super::dvd::idvd(d, k, of_gkb_c);
    let gkb_c = d.mul(gkb, na_c);
    let mid_ty = d.dvd(na_k, gkb_c);
    let nb_c = d.mul(na_b, na_c);
    let rhs_ty = d.dvd(na_k, nb_c);
    let rhs_a = super::dvd::idvd(d, k, bc);

    let step1 = iff_trans(d, &p, lhs_a, mid_ty, rhs_ty, left, core);
    let right_rev = iff_symm(d, &p, rhs_a, rhs_ty, right);
    iff_trans(d, &p, lhs_a, rhs_ty, rhs_a, step1, right_rev)
}

// ---------------------------------------------------------------------------
// The three declared theorems.
// ---------------------------------------------------------------------------

/// Declares `Int.dvd_gcd_mul_iff_dvd_mul`, `Int.dvd_mul_gcd_iff_dvd_mul`, and
/// `Int.dvd_gcd_mul_gcd_iff_dvd_mul` — see the module doc. Must run after
/// `gcd.rs` (`Int.gcd`, `nat_abs_mul`, the two `natAbs`/`dvd` bridges) and
/// after `nat_prelude`'s `dvd_gcd_mul_iff_dvd_mul`/`dvd_mul_gcd_iff_dvd_mul`
/// are declared (they always are, by the time `Int`'s prelude builds, since
/// `Nat`'s prelude is a dependency of `Int`'s).
///
/// # Errors
///
/// Returns the trusted gate's rejection if any constructed term does not
/// type-check.
pub(super) fn declare_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // `Int.dvd_gcd_mul_iff_dvd_mul : ∀ k n m, k ∣ ↑(k.gcd n) * m ↔ k ∣ n * m`
    // -- `F:ml430-int-dvd-gcd-mul-iff-dvd-mul-12f61b99`. The shape directly.
    d.int_theorem(p.dvd_gcd_mul_iff_dvd_mul, 3, &|d, values| {
        let (k, n, m) = (values[0], values[1], values[2]);
        let p = d.int();
        let result = int_dvd_gcd_scaled_iff(d, &p, k, n, m);
        let gkn = igcd(d, k, n);
        let of_gkn = d.of_nat(gkn);
        let prod1 = d.imul(of_gkn, m);
        let lhs = super::dvd::idvd(d, k, prod1);
        let prod2 = d.imul(n, m);
        let rhs = super::dvd::idvd(d, k, prod2);
        (d.const_app(p.logic.iff, &[lhs, rhs]), result)
    })?;

    // `Int.dvd_mul_gcd_iff_dvd_mul : ∀ k n m, k ∣ n * ↑(k.gcd m) ↔ k ∣ n * m`
    // -- `F:ml430-int-dvd-mul-gcd-iff-dvd-mul-22d6488e`. The scaling factor
    // is on the LEFT of the shape (applied at (b,c) := (m,n)), so commute
    // both sides into place.
    d.int_theorem(p.dvd_mul_gcd_iff_dvd_mul, 3, &|d, values| {
        let (k, n, m) = (values[0], values[1], values[2]);
        let p = d.int();
        let base = int_dvd_gcd_scaled_iff(d, &p, k, m, n);
        // base : Iff (idvd k (ofgkm*n)) (idvd k (m*n))

        let gkm = igcd(d, k, m);
        let of_gkm = d.of_nat(gkm);
        let ofgkm_n = d.imul(of_gkm, n);
        let n_ofgkm = d.imul(n, of_gkm);
        let mn = d.imul(m, n);
        let nm = d.imul(n, m);

        let comm_left = d.const_app(p.mul_comm, &[of_gkm, n]); // Eq Int ofgkm_n n_ofgkm
        let left_iff = pred_iff_of_eq_int(d, &p, ofgkm_n, n_ofgkm, comm_left, &|d, v| {
            super::dvd::idvd(d, k, v)
        });
        // left_iff : Iff (idvd k ofgkm_n) (idvd k n_ofgkm)

        let dvd_ofgkm_n = super::dvd::idvd(d, k, ofgkm_n);
        let dvd_n_ofgkm = super::dvd::idvd(d, k, n_ofgkm);
        let left_iff_rev = iff_symm(d, &p, dvd_ofgkm_n, dvd_n_ofgkm, left_iff);
        // left_iff_rev : Iff (idvd k n_ofgkm) (idvd k ofgkm_n)

        let comm_right = d.const_app(p.mul_comm, &[m, n]); // Eq Int mn nm
        let right_iff =
            pred_iff_of_eq_int(d, &p, mn, nm, comm_right, &|d, v| super::dvd::idvd(d, k, v));
        // right_iff : Iff (idvd k mn) (idvd k nm)

        let dvd_mn = super::dvd::idvd(d, k, mn);
        let dvd_nm = super::dvd::idvd(d, k, nm);

        let step1 = iff_trans(d, &p, dvd_n_ofgkm, dvd_ofgkm_n, dvd_mn, left_iff_rev, base);
        let result = iff_trans(d, &p, dvd_n_ofgkm, dvd_mn, dvd_nm, step1, right_iff);

        (d.const_app(p.logic.iff, &[dvd_n_ofgkm, dvd_nm]), result)
    })?;

    // `Int.dvd_gcd_mul_gcd_iff_dvd_mul :
    //   ∀ k n m, k ∣ ↑(k.gcd n) * ↑(k.gcd m) ↔ k ∣ n * m` --
    // `F:ml430-int-dvd-gcd-mul-gcd-iff-dvd-mul-8ea752a5`. The shape at
    // (b,c) := (n, ofNat (k.gcd m)), then chain against
    // `dvd_mul_gcd_iff_dvd_mul`.
    d.int_theorem(p.dvd_gcd_mul_gcd_iff_dvd_mul, 3, &|d, values| {
        let (k, n, m) = (values[0], values[1], values[2]);
        let p = d.int();
        let gkm = igcd(d, k, m);
        let of_gkm = d.of_nat(gkm);
        let base = int_dvd_gcd_scaled_iff(d, &p, k, n, of_gkm);
        // base : Iff (idvd k (ofgkn * ofgkm)) (idvd k (n * ofgkm))

        let tail = d.lemma(p.dvd_mul_gcd_iff_dvd_mul, &[k, n, m]);
        // tail : Iff (idvd k (n * ofgkm)) (idvd k (n*m))

        let gkn = igcd(d, k, n);
        let of_gkn = d.of_nat(gkn);
        let lhs_prod = d.imul(of_gkn, of_gkm);
        let mid_prod = d.imul(n, of_gkm);
        let nm = d.imul(n, m);

        let lhs_ty = super::dvd::idvd(d, k, lhs_prod);
        let mid_ty = super::dvd::idvd(d, k, mid_prod);
        let rhs_ty = super::dvd::idvd(d, k, nm);

        let result = iff_trans(d, &p, lhs_ty, mid_ty, rhs_ty, base, tail);
        (d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]), result)
    })?;

    Ok(())
}
