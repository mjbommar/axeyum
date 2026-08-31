//! `Int.gcd` — Euclid's Book VII transported from the proved, axiom-free `ℕ`
//! development (`nat_prelude::gcd`, `nat_prelude::bezout`) across `natAbs`.
//!
//! `Int.gcd a b := Nat.gcd (natAbs a) (natAbs b)` (Mathlib's convention: a
//! `Nat`-valued gcd of two integers). Everything here is a genuine transport,
//! not a re-derivation: the executable Euclidean recurrence, the
//! greatest-common-divisor characterization, and Bézout's identity are all
//! already proved over `ℕ`; the work in this module is exactly the sign
//! bookkeeping `natAbs` introduces.
//!
//! Two bridge lemmas do essentially all of that bookkeeping, and both are
//! exposed because both directions are needed more than once:
//!
//! - [`declare_dvd_of_nat_abs_dvd`]: `Nat` divisibility of two magnitudes
//!   lifts to `Int` divisibility of the signed values, **regardless of either
//!   side's sign** (`natAbs x ∣ natAbs y → x ∣ y`). This is what turns
//!   `Nat.gcd_dvd_left`/`Nat.gcd_dvd_right` into `gcd_dvd_left`/`gcd_dvd_right`,
//!   and closes `dvd_gcd`.
//! - [`declare_nat_abs_dvd_nat_abs_of_dvd`]: the reverse direction
//!   (`a ∣ b → natAbs a ∣ natAbs b`), needed to feed `Nat.dvd_gcd` from
//!   `dvd_gcd`'s `Int.dvd` hypotheses.
//!
//! Both rest on [`declare_nat_abs_mul`] (`natAbs (a*b) = natAbs a * natAbs b`),
//! proved by the same four-branch `Int.rec` case split `nat_abs.rs` uses, reusing
//! `nat_abs_neg_of_nat` for the two sign-mixed branches and closing the two
//! sign-matched branches by `rfl`.
//!
//! Bézout ([`declare_gcd_eq_gcd_ab`]) is the one place genuine new algebra is
//! needed: `Nat.gcd_bezout`'s balanced witnesses cast cleanly into `ℤ` (casting
//! commutes with `+`/`*` on `ofNat`-wrapped terms by pure computation), but
//! turning the cast equation into `ofNat g = a*u + b*v` for **signed** `a,b`
//! needs `u,v` to flip sign against `a,b`. That needs `Int.neg`'s ring
//! properties (`(-a)*b = -(a*b)`, `a*(-b) = -(a*b)`, `-(-a) = a`) in general —
//! not just against `negOfNat`, which is all the base development proves —
//! so this module derives those three from `neg_one_mul`/`mul_assoc`/`mul_comm`/
//! `one_mul` first.

use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::defs::DERIVED_HEIGHT;
use super::ops::{Branch, IntDev, Shape, case_split, exists_elim};

// ---------------------------------------------------------------------------
// Small local term-building helpers.
// ---------------------------------------------------------------------------

/// `Int.natAbs a`.
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().nat_abs;
    d.const_app(f, &[a])
}

/// `Int.gcd a b`.
fn igcd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().gcd;
    d.const_app(f, &[a, b])
}

/// `fun (c : Int) => Eq Int b (a * c)` — the predicate `Int.dvd a b`
/// existentially quantifies (mirrors `dvd.rs`'s private helper of the same
/// shape; not shared because it is five lines and `dvd.rs` does not expose it).
fn idvd_predicate(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ac = d.imul(a, c);
    let body = d.ieq(b, ac);
    d.lam_fv(c_fv, int_ty, body)
}

/// `Int.dvd a b`.
fn idvd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().dvd;
    d.const_app(f, &[a, b])
}

/// `Exists.intro.{1} Int (idvd_predicate a b) witness proof : Int.dvd a b`.
fn idvd_intro(d: &mut IntDev<'_>, a: ExprId, b: ExprId, witness: ExprId, proof: ExprId) -> ExprId {
    let pred = idvd_predicate(d, a, b);
    let one = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    let int_ty = d.int_ty();
    d.apply(intro, &[int_ty, pred, witness, proof])
}

/// Eliminate `witness : Int.dvd a b` into `target`, given
/// `minor : ∀ (c : Int), Eq Int b (a*c) → target`.
fn idvd_elim(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let pred = idvd_predicate(d, a, b);
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_ty = {
        let name = d.int().logic.exists_;
        let e = d.kernel().const_(name, vec![one]);
        d.apply(e, &[int_ty, pred])
    };
    let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, pred, motive, minor, witness])
}

/// `Exists.intro.{1} Nat (dvd_predicate a n) witness proof : Nat.dvd a n`.
fn nat_dvd_intro(
    d: &mut IntDev<'_>,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let pred = d.dvd_predicate(a, n);
    let one = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    let nat = d.nat_ty();
    d.apply(intro, &[nat, pred, witness, proof])
}

/// From `h : Eq Int p q` and an `Int -> Nat` context `f`, derive
/// `Eq Nat (f p) (f q)`. The `Int`-side counterpart of [`NatOps::congr`],
/// which is fixed to `Nat -> Nat` contexts.
fn icongr_nat(
    d: &mut IntDev<'_>,
    p: ExprId,
    q: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fp = f(d, p);
    let motive = d.ieq_motive(p, &|d, x| {
        let fx = f(d, x);
        d.eq(fp, fx)
    });
    let refl_case = d.refl(fp);
    d.itransport(p, motive, refl_case, q, h)
}

// ---------------------------------------------------------------------------
// `Int.gcd`.
// ---------------------------------------------------------------------------

/// Admit `Int.gcd : Int → Int → Nat := fun a b => Nat.gcd (natAbs a) (natAbs b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_gcd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let big_a = nat_abs(d, a);
    let big_b = nat_abs(d, b);
    let body = NatOps::gcd(d, big_a, big_b);
    let value = {
        let inner = d.lam_fv(b_fv, int_ty, body);
        d.lam_fv(a_fv, int_ty, inner)
    };
    let ty = {
        let inner = d.arrow(int_ty, nat);
        d.arrow(int_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.gcd,
        uparams: vec![],
        ty,
        value,
        hint: crate::env::ReducibilityHint::Regular(6),
    })
}

// ---------------------------------------------------------------------------
// `Nat.dvd` antisymmetry — the shared engine behind `gcd_comm` and
// `gcd_zero_right`, neither of which has a ready-made `Nat.gcd_comm` or
// `Nat.gcd_zero_right` to transport (this development has no such lemma; only
// `gcd_zero_left`, `gcd_dvd_left/right`, and `dvd_gcd`).
// Corrected 2026-08-31, kernel-measured: `Nat.gcd_comm` now exists (landed
// after this comment was written); `Nat.gcd_zero_right` still does not.
// <!-- was-absent: Nat.gcd_comm -->
// <!-- absent: Nat.gcd_zero_right -->
// ---------------------------------------------------------------------------

/// `fun (h1 : ty1) (h2 : ty2) => body(h1, h2)`.
fn with_two_hypotheses(
    d: &mut IntDev<'_>,
    ty1: ExprId,
    ty2: ExprId,
    body: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let inner = body(d, h1, h2);
    let with_h2 = d.lam_fv(h2_fv, ty2, inner);
    d.lam_fv(h1_fv, ty1, with_h2)
}

/// From `hxy : Nat.dvd x y` and `hyx : Nat.dvd y x`, derive `Eq Nat x y`.
///
/// A general antisymmetry of `Nat.dvd` this development has not needed
/// before, built once by `Nat.rec` on `x` (holding `y` fixed): the zero
/// branch eliminates `dvd 0 y` directly (`y = 0*c = 0`, via `Nat.zero_mul`),
/// and the successor branch (`x = succ k`, so `1 ≤ x` by `Nat.zero_lt_succ`)
/// gets `1 ≤ y` from `Nat.one_le_of_dvd_pos`, then both bounds from
/// `Nat.le_of_dvd`, and closes with `Nat.le_antisymm`. Nothing here looks at
/// how `x`/`y` were computed — it is not a re-derivation of Euclid's
/// algorithm, just the standard "mutual divisibility is equality" argument
/// from lemmas this prelude already has.
fn nat_dvd_antisymm(d: &mut IntDev<'_>, x: ExprId, y: ExprId, hxy: ExprId, hyx: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, w: ExprId| {
        let fwd = NatOps::dvd(d, w, y);
        let back = NatOps::dvd(d, y, w);
        let goal = d.eq(w, y);
        let inner = d.arrow(back, goal);
        d.arrow(fwd, inner)
    };
    let base = |d: &mut IntDev<'_>| {
        let zero = d.zero();
        let fwd_ty = NatOps::dvd(d, zero, y);
        let back_ty = NatOps::dvd(d, y, zero);
        with_two_hypotheses(d, fwd_ty, back_ty, &|d, fwd, _back| {
            let nat = d.nat_ty();
            let pred = d.dvd_predicate(zero, y);
            let goal = d.eq(zero, y);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let zc = NatOps::mul(d, zero, c);
            let eqc_ty = d.eq(y, zc);
            let eqc_fv = d.fresh_fvar();
            let eqc = d.kernel().fvar(eqc_fv);
            let zero_mul_eq = {
                let name = d.int().nat.zero_mul;
                d.const_app(name, &[c])
            };
            let (_, chained) = d.chain(y, &[(zc, eqc), (zero, zero_mul_eq)]);
            let flipped = d.symm(y, zero, chained);
            let with_eqc = d.lam_fv(eqc_fv, eqc_ty, flipped);
            let minor = d.lam_fv(c_fv, nat, with_eqc);
            exists_elim(d, pred, goal, fwd, minor)
        })
    };
    let step = |d: &mut IntDev<'_>, k: ExprId, _ih: ExprId| {
        let sk = d.succ(k);
        let fwd_ty = NatOps::dvd(d, sk, y);
        let back_ty = NatOps::dvd(d, y, sk);
        with_two_hypotheses(d, fwd_ty, back_ty, &|d, fwd, back| {
            let h_pos = {
                let name = d.int().nat.zero_lt_succ;
                d.const_app(name, &[k])
            };
            let one_le_y = {
                let name = d.int().nat.one_le_of_dvd_pos;
                d.const_app(name, &[y, sk, h_pos, back])
            };
            let y_le_sk = {
                let name = d.int().nat.le_of_dvd;
                d.const_app(name, &[y, sk, h_pos, back])
            };
            let sk_le_y = {
                let name = d.int().nat.le_of_dvd;
                d.const_app(name, &[sk, y, one_le_y, fwd])
            };
            let name = d.int().nat.le_antisymm;
            d.const_app(name, &[sk, y, sk_le_y, y_le_sk])
        })
    };
    let implication = d.induct(&motive, &base, &step, x);
    d.apply(implication, &[hxy, hyx])
}

/// `gcd_comm : ∀ (a b : Int), Eq Nat (gcd a b) (gcd b a)`.
///
/// Both `Int.gcd a b` and `Int.gcd b a` unfold to `Nat.gcd (natAbs a)
/// (natAbs b)`/`Nat.gcd (natAbs b) (natAbs a)`; mutual divisibility comes
/// straight from `Nat.gcd_dvd_left`/`Nat.gcd_dvd_right`/`Nat.dvd_gcd` (no
/// `natAbs`/`Int.dvd` bridging needed, since everything here is already
/// `Nat`-valued), and [`nat_dvd_antisymm`] closes it.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_gcd_comm(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_comm, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let m = nat_abs(d, a);
        let n = nat_abs(d, b);
        let stmt = {
            let lhs = igcd(d, a, b);
            let rhs = igcd(d, b, a);
            d.eq(lhs, rhs)
        };
        let g1 = NatOps::gcd(d, m, n);
        let g2 = NatOps::gcd(d, n, m);
        let g1_dvd_m = d.const_app(p.nat.gcd_dvd_left, &[m, n]);
        let g1_dvd_n = d.const_app(p.nat.gcd_dvd_right, &[m, n]);
        let g2_dvd_n = d.const_app(p.nat.gcd_dvd_left, &[n, m]);
        let g2_dvd_m = d.const_app(p.nat.gcd_dvd_right, &[n, m]);
        let hxy = d.const_app(p.nat.dvd_gcd, &[g1, n, m, g1_dvd_n, g1_dvd_m]);
        let hyx = d.const_app(p.nat.dvd_gcd, &[g2, m, n, g2_dvd_m, g2_dvd_n]);
        let proof = nat_dvd_antisymm(d, g1, g2, hxy, hyx);
        (stmt, proof)
    })?;
    Ok(())
}

/// `gcd_one_right : ∀ (a : Int), Eq Nat (gcd a one) one` and
/// `gcd_zero_right : ∀ (a : Int), Eq Nat (gcd a zero) (natAbs a)`.
///
/// `gcd_one_right`: `gcd a 1 ∣ 1` (`gcd_dvd_right`) already IS a `Nat` divisor
/// of `1`, so `Nat.eq_one_of_dvd_one` closes it with no antisymmetry needed.
///
/// `gcd_zero_right`: `gcd a 0 ∣ natAbs a` (`gcd_dvd_left`) and `natAbs a ∣
/// gcd a 0` (`Nat.dvd_gcd` fed by `Nat.dvd_refl`/`Nat.dvd_zero`), closed by
/// [`nat_dvd_antisymm`] — the same engine `gcd_comm` uses, not a repeat of
/// the Euclidean recursion.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_gcd_one_zero_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_one_right, 1, &|d, v| {
        let a = v[0];
        let one_i = d.ione();
        let one_n = d.num(1);
        let stmt = {
            let g = igcd(d, a, one_i);
            d.eq(g, one_n)
        };
        let big_a = nat_abs(d, a);
        let g = NatOps::gcd(d, big_a, one_n);
        let dvd_one = d.const_app(p.nat.gcd_dvd_right, &[big_a, one_n]);
        let proof = d.const_app(p.nat.eq_one_of_dvd_one, &[g, dvd_one]);
        (stmt, proof)
    })?;
    d.int_theorem(p.gcd_zero_right, 1, &|d, v| {
        let a = v[0];
        let zero_i = d.izero();
        let zero_n = d.zero();
        let m = nat_abs(d, a);
        let stmt = {
            let g = igcd(d, a, zero_i);
            d.eq(g, m)
        };
        let g = NatOps::gcd(d, m, zero_n);
        let g_dvd_m = d.const_app(p.nat.gcd_dvd_left, &[m, zero_n]);
        let m_dvd_m = d.const_app(p.nat.dvd_refl, &[m]);
        let m_dvd_zero = d.const_app(p.nat.dvd_zero, &[m]);
        let m_dvd_g = d.const_app(p.nat.dvd_gcd, &[m, m, zero_n, m_dvd_m, m_dvd_zero]);
        let proof = nat_dvd_antisymm(d, g, m, g_dvd_m, m_dvd_g);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `natAbs` is multiplicative.
// ---------------------------------------------------------------------------

/// `nat_abs_mul : ∀ (a b : Int), natAbs (a*b) = natAbs a * natAbs b`.
///
/// All four `Int.rec` branches of `a*b` are pinned by `defs.rs`'s
/// `define_binary_int` for `Int.mul`: the sign-matched branches (`ofNat*ofNat`,
/// `negSucc*negSucc`) land back on `ofNat _`, so both sides reduce to the same
/// `Nat` product by `rfl`; the sign-mixed branches land on `negOfNat _` for a
/// **non-constant** `Nat` argument, so those two branches go through
/// `nat_abs_neg_of_nat` instead (exactly why that lemma needed induction rather
/// than `rfl`, in `nat_abs.rs`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_mul, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (a, b) = (args[0], args[1]);
            let product = d.imul(a, b);
            let lhs = nat_abs(d, product);
            let na = nat_abs(d, a);
            let nb = nat_abs(d, b);
            let rhs = NatOps::mul(d, na, nb);
            d.eq(lhs, rhs)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, &[a, b], &statement, &|d, branches: &[Branch]| {
            let (shape_a, na_field) = branches[0];
            let (shape_b, nb_field) = branches[1];
            match (shape_a, shape_b) {
                (Shape::OfNat, Shape::OfNat) => {
                    let product = NatOps::mul(d, na_field, nb_field);
                    d.refl(product)
                }
                (Shape::OfNat, Shape::NegSucc) => {
                    let succ_n = d.succ(nb_field);
                    let prod = NatOps::mul(d, na_field, succ_n);
                    d.lemma(p.nat_abs_neg_of_nat, &[prod])
                }
                (Shape::NegSucc, Shape::OfNat) => {
                    let succ_m = d.succ(na_field);
                    let prod = NatOps::mul(d, succ_m, nb_field);
                    d.lemma(p.nat_abs_neg_of_nat, &[prod])
                }
                (Shape::NegSucc, Shape::NegSucc) => {
                    let succ_m = d.succ(na_field);
                    let succ_n = d.succ(nb_field);
                    let product = NatOps::mul(d, succ_m, succ_n);
                    d.refl(product)
                }
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The two `natAbs`/`dvd` bridges.
// ---------------------------------------------------------------------------

/// `dvd_of_nat_abs_dvd : ∀ (x y : Int), natAbs x ∣ natAbs y → x ∣ y`.
///
/// The general bridge, sign-flexible on **both** sides: case-split on `x` and
/// `y` (four branches). The witness is `ofNat q` when `x, y` have the same
/// sign and `neg (ofNat q)` when they differ — the ordinary "signs cancel"
/// rule for integer divisibility, made concrete by which of the existing
/// `Int.mul` computation rules (`ofNat*ofNat`, `negSucc*negOfNat`,
/// `negSucc*ofNat`, `negSucc*negSucc`, all pinned in `defs.rs`) matches.
///
/// This single lemma covers both directions this development needs:
/// `gcd_dvd_left`/`_right` instantiate it with `x = ofNat (gcd a b)` (already
/// non-negative — the `OfNat` branch of `x` fires trivially) and `y = a`/`b`
/// (sign-flexible); `dvd_gcd`'s closing step instantiates it with `x = c`
/// (sign-flexible) and `y = ofNat (gcd a b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_dvd_of_nat_abs_dvd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_of_nat_abs_dvd, 2, &|d, v| {
        let (x, y) = (v[0], v[1]);
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (x, y) = (args[0], args[1]);
            let big_x = nat_abs(d, x);
            let big_y = nat_abs(d, y);
            let hyp = d.dvd(big_x, big_y);
            let concl = idvd(d, x, y);
            d.arrow(hyp, concl)
        };
        let stmt = statement(d, v);
        let nat = d.nat_ty();
        let proof = case_split(d, &[x, y], &statement, &|d, branches: &[Branch]| {
            let (shape_x, field_x) = branches[0];
            let (shape_y, field_y) = branches[1];
            // `x_term`/`y_term` are the branch's own constructor applications
            // (matching what `case_split` substituted into `statement`);
            // `negate` says whether the witness needs to flip sign relative to
            // `y`'s cast (exactly when `x`, `y` disagree in sign).
            let (x_term, big_x, negate_x) = match shape_x {
                Shape::OfNat => (d.of_nat(field_x), field_x, false),
                Shape::NegSucc => (d.neg_succ(field_x), d.succ(field_x), true),
            };
            let (y_term, big_y, negate_y) = match shape_y {
                Shape::OfNat => (d.of_nat(field_y), field_y, false),
                Shape::NegSucc => (d.neg_succ(field_y), d.succ(field_y), true),
            };
            let negate = negate_x != negate_y;

            let hyp_ty = d.dvd(big_x, big_y);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let pred = d.dvd_predicate(big_x, big_y);
            let target = idvd(d, x_term, y_term);

            let minor = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let eq_fv = d.fresh_fvar();
                let prod = NatOps::mul(d, big_x, q);
                let eq_ty = d.eq(big_y, prod);
                let eq_h = d.kernel().fvar(eq_fv);

                // `target_of_prod` is `ofNat prod` when `y ≥ 0`, `negOfNat prod`
                // when `y < 0` — chosen so `f`'s image at `big_y` is defeq to
                // `y_term` (`ofNat field_y` outright, or `negOfNat (succ
                // field_y)` reducing to `negSucc field_y` by `rfl`).
                let (target_of_prod, cast) = match shape_y {
                    Shape::OfNat => {
                        let of_prod = d.of_nat(prod);
                        let cast = d.nat_eq_to_int(big_y, prod, eq_h, &|d, z| d.of_nat(z));
                        (of_prod, cast)
                    }
                    Shape::NegSucc => {
                        let negof_prod = d.neg_of_nat(prod);
                        let cast = d.nat_eq_to_int(big_y, prod, eq_h, &|d, z| d.neg_of_nat(z));
                        (negof_prod, cast)
                    }
                };
                // `cast : Eq Int (f big_y) (f prod)`, defeq to
                // `Eq Int y_term target_of_prod`.

                let (witness, final_eq) = if negate {
                    // witness = neg (ofNat q), definitionally `negOfNat q`.
                    let of_q = d.of_nat(q);
                    let witness = d.ineg(of_q);
                    let xw = d.imul(x_term, witness);
                    let mul_eq = match (shape_x, shape_y) {
                        // x nonneg, y negative: ofNat m * negOfNat q = negOfNat (m*q).
                        (Shape::OfNat, Shape::NegSucc) => {
                            d.lemma(p.mul_of_nat_neg_of_nat, &[big_x, q])
                        }
                        // x negative, y nonneg: negSucc m * negOfNat q = ofNat ((m+1)*q).
                        (Shape::NegSucc, Shape::OfNat) => {
                            d.lemma(p.mul_neg_succ_neg_of_nat, &[field_x, q])
                        }
                        _ => unreachable!("negate is only set on mixed-sign branches"),
                    };
                    // `mul_eq : Eq Int xw target_of_prod` (up to `witness`'s
                    // defeq to `negOfNat q`).
                    let symm_mul_eq = d.isymm(xw, target_of_prod, mul_eq);
                    let final_eq = d.itrans(y_term, target_of_prod, xw, cast, symm_mul_eq);
                    (witness, final_eq)
                } else {
                    // witness = ofNat q; `x_term * ofNat q` reduces (rfl)
                    // directly to `target_of_prod`, so `cast` alone (up to that
                    // defeq) already proves `Eq Int y_term xw`.
                    let witness = d.of_nat(q);
                    (witness, cast)
                };
                let body = idvd_intro(d, x_term, y_term, witness, final_eq);
                let with_eq = d.lam_fv(eq_fv, eq_ty, body);
                d.lam_fv(q_fv, nat, with_eq)
            };
            let eliminated = {
                let anon = d.anon_name();
                let one = d.level_one();
                let exists_name = d.int().logic.exists_;
                let exists_ty = {
                    let e = d.kernel().const_(exists_name, vec![one]);
                    d.apply(e, &[nat, pred])
                };
                let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
                let rec_name = d.int().logic.exists_rec;
                let rec = d.kernel().const_(rec_name, vec![one]);
                d.apply(rec, &[nat, pred, motive, minor, h])
            };
            d.lam_fv(h_fv, hyp_ty, eliminated)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `nat_abs_dvd_nat_abs_of_dvd : ∀ (a b : Int), a ∣ b → natAbs a ∣ natAbs b`.
///
/// The reverse bridge: eliminate the `Int.dvd` witness `c` (`b = a*c`), and
/// transport the equation to `Nat` by `natAbs`, then rewrite `natAbs (a*c)` by
/// [`declare_nat_abs_mul`]. The `Nat.dvd` witness is `natAbs c`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_dvd_nat_abs_of_dvd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_dvd_nat_abs_of_dvd, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp_ty = idvd(d, a, b);
        let big_a = nat_abs(d, a);
        let big_b = nat_abs(d, b);
        let target = d.dvd(big_a, big_b);
        let stmt = d.arrow(hyp_ty, target);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let minor = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let ac = d.imul(a, c);
            let eq_fv = d.fresh_fvar();
            let eq_ty = d.ieq(b, ac);
            let eq_h = d.kernel().fvar(eq_fv);
            let big_c = nat_abs(d, c);

            let step1 = icongr_nat(d, b, ac, eq_h, &|d, x| nat_abs(d, x));
            let step2 = d.lemma(p.nat_abs_mul, &[a, c]);
            let nat_abs_ac = nat_abs(d, ac);
            let mul_ab = NatOps::mul(d, big_a, big_c);
            let combined = d.trans(big_b, nat_abs_ac, mul_ab, step1, step2);
            let witness_proof = nat_dvd_intro(d, big_a, big_b, big_c, combined);
            let with_eq = d.lam_fv(eq_fv, eq_ty, witness_proof);
            let int_ty = d.int_ty();
            d.lam_fv(c_fv, int_ty, with_eq)
        };
        let eliminated = idvd_elim(d, a, b, target, h, minor);
        let proof = d.lam_fv(h_fv, hyp_ty, eliminated);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The universal property: `gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`.
// ---------------------------------------------------------------------------

/// `gcd_dvd_left : ∀ (a b : Int), ofNat (gcd a b) ∣ a` and
/// `gcd_dvd_right : ∀ (a b : Int), ofNat (gcd a b) ∣ b`.
///
/// Both are `dvd_of_nat_abs_dvd` applied to `Nat.gcd_dvd_left`/
/// `Nat.gcd_dvd_right`: `natAbs (ofNat (gcd a b))` reduces to `gcd a b` (i.e.
/// `Nat.gcd (natAbs a) (natAbs b)`) by `rfl`, which is exactly what
/// `Nat.gcd_dvd_left`/`_right` conclude divides `natAbs a`/`natAbs b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_gcd_dvd_left_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_dvd_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let big_a = nat_abs(d, a);
        let big_b = nat_abs(d, b);
        let g = igcd(d, a, b);
        let of_g = d.of_nat(g);
        let stmt = idvd(d, of_g, a);
        let nat_dvd = d.lemma(p.nat.gcd_dvd_left, &[big_a, big_b]);
        let proof = d.const_app(p.dvd_of_nat_abs_dvd, &[of_g, a, nat_dvd]);
        (stmt, proof)
    })?;
    d.int_theorem(p.gcd_dvd_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let big_a = nat_abs(d, a);
        let big_b = nat_abs(d, b);
        let g = igcd(d, a, b);
        let of_g = d.of_nat(g);
        let stmt = idvd(d, of_g, b);
        let nat_dvd = d.lemma(p.nat.gcd_dvd_right, &[big_a, big_b]);
        let proof = d.const_app(p.dvd_of_nat_abs_dvd, &[of_g, b, nat_dvd]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `dvd_gcd : ∀ (c a b : Int), c ∣ a → c ∣ b → c ∣ ofNat (gcd a b)`.
///
/// Together with [`declare_gcd_dvd_left_right`], this is the universal
/// property that makes `gcd` *the* greatest common divisor: convert both
/// hypotheses to `Nat.dvd` via [`declare_nat_abs_dvd_nat_abs_of_dvd`], combine
/// with `Nat.dvd_gcd`, and lift back via [`declare_dvd_of_nat_abs_dvd`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_dvd_gcd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_gcd, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let h1_ty = idvd(d, c, a);
        let h2_ty = idvd(d, c, b);
        let g = igcd(d, a, b);
        let of_g = d.of_nat(g);
        let goal = idvd(d, c, of_g);
        let arrow2 = d.arrow(h2_ty, goal);
        let stmt = d.arrow(h1_ty, arrow2);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let big_c = nat_abs(d, c);
        let big_a = nat_abs(d, a);
        let big_b = nat_abs(d, b);
        let n1 = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[c, a, h1]);
        let n2 = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[c, b, h2]);
        let nat_dvd_gcd = d.lemma(p.nat.dvd_gcd, &[big_c, big_a, big_b]);
        let nat_dvd = d.apply(nat_dvd_gcd, &[n1, n2]);
        let proof_body = d.const_app(p.dvd_of_nat_abs_dvd, &[c, of_g, nat_dvd]);

        let with_h2 = d.lam_fv(h2_fv, h2_ty, proof_body);
        let proof = d.lam_fv(h1_fv, h1_ty, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.ne_zero_of_gcd` and the two `gcd_mul_right` coprimality descents.
// ---------------------------------------------------------------------------

/// `ne_zero_of_gcd : ∀ (x y : Int), Not (Eq Nat (gcd x y) zero) →
/// Or (Not (Eq Int x zero)) (Not (Eq Int y zero))`.
///
/// `Int.eq_em x zero` splits on whether `x = 0`. The `x ≠ 0` branch is
/// `Or.inl` directly. The `x = 0` branch (`hx`) builds `y ≠ 0` as a bare
/// lambda: assume `hy : y = 0`; `gcd_zero_right zero` gives `gcd 0 0 = natAbs
/// 0`, definitionally `gcd 0 0 = 0`, and rewriting that along `hx`/`hy` (via
/// `int_eq_rewrite`, twice) produces `gcd x y = 0`, which contradicts the
/// hypothesis.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_ne_zero_of_gcd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.ne_zero_of_gcd, 2, &|d, v| {
        let (x, y) = (v[0], v[1]);
        let zero_nat = d.zero();
        let zero_int = d.izero();
        let g = igcd(d, x, y);
        let gcd_ne_zero_ty = {
            let eq_ty = d.eq(g, zero_nat);
            d.not(eq_ty)
        };
        let x_ne_zero = {
            let eq_ty = d.ieq(x, zero_int);
            d.not(eq_ty)
        };
        let y_ne_zero = {
            let eq_ty = d.ieq(y, zero_int);
            d.not(eq_ty)
        };
        let concl = d.or(x_ne_zero, y_ne_zero);
        let stmt = d.arrow(gcd_ne_zero_ty, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let hx_ty = d.ieq(x, zero_int);
        let hx_not_ty = d.not(hx_ty);
        let em_x = d.lemma(p.eq_em, &[x, zero_int]);

        let on_left = &|d: &mut IntDev<'_>, hx: ExprId| -> ExprId {
            let hy_fv = d.fresh_fvar();
            let hy = d.kernel().fvar(hy_fv);
            let hy_ty = d.ieq(y, zero_int);

            let base = d.lemma(p.gcd_zero_right, &[zero_int]);
            let motive_y = &|d: &mut IntDev<'_>, w: ExprId| -> ExprId {
                let gw = igcd(d, zero_int, w);
                d.eq(gw, zero_nat)
            };
            let isymm_hy = d.isymm(y, zero_int, hy);
            let step2 = d.int_eq_rewrite(zero_int, y, isymm_hy, base, motive_y);

            let motive_x = &|d: &mut IntDev<'_>, w: ExprId| -> ExprId {
                let gw = igcd(d, w, y);
                d.eq(gw, zero_nat)
            };
            let isymm_hx = d.isymm(x, zero_int, hx);
            let gcd_xy_eq_0 = d.int_eq_rewrite(zero_int, x, isymm_hx, step2, motive_x);

            let false_proof = d.apply(h, &[gcd_xy_eq_0]);
            let not_y = d.lam_fv(hy_fv, hy_ty, false_proof);
            d.or_inr(x_ne_zero, y_ne_zero, not_y)
        };
        let on_right = &|d: &mut IntDev<'_>, hx_not: ExprId| -> ExprId {
            d.or_inl(x_ne_zero, y_ne_zero, hx_not)
        };
        let disj = d.or_elim(hx_ty, hx_not_ty, concl, em_x, on_left, on_right);
        let proof = d.lam_fv(h_fv, gcd_ne_zero_ty, disj);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.mul (ofNat m) (ofNat n)` reduces to `ofNat (mul m n)` by ι-reduction
/// (`define_binary_int`'s ofNat/ofNat branch computes `Nat.mul` directly), so
/// `Int.gcd a (↑m * ↑n)` unfolds to `Nat.gcd (natAbs a) (m*n)` purely by
/// computation — no cast lemma is needed to bridge it.
///
/// Declares both `gcd_eq_one_of_gcd_mul_right_eq_one_left` and its right-hand
/// mirror in one pass, since both share the cast-erasure argument above and
/// differ only in which of `Nat.dvd_mul`'s two divisibility facts
/// (`m ∣ m*n` directly, `n ∣ n*m` transported by `Nat.mul_comm` to `n ∣ m*n`)
/// feeds `Nat.coprime_of_dvd_right`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if either constructed term does not
/// check.
pub(super) fn declare_gcd_eq_one_of_gcd_mul_right_eq_one(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    // Shared statement shape: ∀ (a : Int) (m n : Nat),
    //   Eq Nat (gcd a (ofNat m * ofNat n)) one → Eq Nat (gcd a target) one.
    let build_stmt = |d: &mut IntDev<'_>, a: ExprId, m: ExprId, n: ExprId, target: ExprId| {
        let one = d.num(1);
        let of_m = d.of_nat(m);
        let of_n = d.of_nat(n);
        let mn_int = d.imul(of_m, of_n);
        let hyp = {
            let g = igcd(d, a, mn_int);
            d.eq(g, one)
        };
        let concl = {
            let g = igcd(d, a, target);
            d.eq(g, one)
        };
        d.arrow(hyp, concl)
    };

    let int_ty = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let big_a = nat_abs(d, a);

    // --- left: gcd a (m*n) = 1 → gcd a m = 1 ---
    {
        let of_m = d.of_nat(m);
        let body = build_stmt(d, a, m, n, of_m);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, body);
            let with_m = d.pi_fv(m_fv, nat, with_n);
            d.pi_fv(a_fv, int_ty, with_m)
        };

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let mn = NatOps::mul(d, m, n);
        let dvd_m_mn = d.lemma(p.nat.dvd_mul, &[m, n]);
        let proof_body = d.lemma(p.nat.coprime_of_dvd_right, &[big_a, m, mn, dvd_m_mn, h]);
        let hyp_ty = {
            let (of_m, of_n) = (d.of_nat(m), d.of_nat(n));
            let mn_int = d.imul(of_m, of_n);
            let g = igcd(d, a, mn_int);
            let one = d.num(1);
            d.eq(g, one)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp_ty, proof_body);
            let with_n = d.lam_fv(n_fv, nat, with_h);
            let with_m = d.lam_fv(m_fv, nat, with_n);
            d.lam_fv(a_fv, int_ty, with_m)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.gcd_eq_one_of_gcd_mul_right_eq_one_left,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // --- right: gcd a (m*n) = 1 → gcd a n = 1 ---
    {
        let of_n = d.of_nat(n);
        let body = build_stmt(d, a, m, n, of_n);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, body);
            let with_m = d.pi_fv(m_fv, nat, with_n);
            d.pi_fv(a_fv, int_ty, with_m)
        };

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let nm = NatOps::mul(d, n, m);
        let mn = NatOps::mul(d, m, n);
        let dvd_n_nm = d.lemma(p.nat.dvd_mul, &[n, m]);
        let comm = d.lemma(p.nat.mul_comm, &[n, m]);
        let motive = &|d: &mut IntDev<'_>, w: ExprId| -> ExprId { d.dvd(n, w) };
        let dvd_n_mn = d.nat_rewrite(nm, mn, comm, dvd_n_nm, motive);
        let proof_body = d.lemma(p.nat.coprime_of_dvd_right, &[big_a, n, mn, dvd_n_mn, h]);
        let hyp_ty = {
            let (of_m, of_n) = (d.of_nat(m), d.of_nat(n));
            let mn_int = d.imul(of_m, of_n);
            let g = igcd(d, a, mn_int);
            let one = d.num(1);
            d.eq(g, one)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp_ty, proof_body);
            let with_n = d.lam_fv(n_fv, nat, with_h);
            let with_m = d.lam_fv(m_fv, nat, with_n);
            d.lam_fv(a_fv, int_ty, with_m)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.gcd_eq_one_of_gcd_mul_right_eq_one_right,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// General `Int.neg` ring facts, built here as local proof-term helpers for
// this module's own inline use: `neg_mul`, `mul_neg`, `neg_neg`.
//
// `neg_mul` and `neg_neg` are not declared as public kernel theorems (nothing
// needs them as such). `Int.mul_neg` **is** one — see
// `sub::declare_mul_neg` (`sub.rs`), added for `Int.modEq_iff_dvd` and run
// earlier in the build sequence than anything in this file. The `mul_neg`
// below is a separate, private proof-term builder kept so the derivations in
// this module do not round-trip through the public theorem; it is not the
// same declaration.
// ---------------------------------------------------------------------------

/// `Eq Int (neg (neg x)) x`, for any `x`.
///
/// `neg (neg one) = one` holds by `rfl` (two `Int.rec` computations on the
/// concrete literal `1`, no case split needed since neither reduction depends
/// on a variable), and from there `neg (neg x) = (-1)*(-1)*x = 1*x = x` by
/// `neg_one_mul`/`mul_assoc`/`one_mul` alone.
pub(super) fn neg_neg(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let p = d.int();
    let one_c = d.ione();
    let neg_one = d.ineg(one_c);
    let neg_x = d.ineg(x);
    let neg_neg_x = d.ineg(neg_x);

    // step1 : neg (neg x) = neg_one * neg_x
    let step1 = {
        let fwd = d.const_app(p.neg_one_mul, &[neg_x]); // (neg_one*neg_x) = neg(neg x)
        let mul_negone_negx = d.imul(neg_one, neg_x);
        d.isymm(mul_negone_negx, neg_neg_x, fwd)
    };
    let mul_negone_negx = d.imul(neg_one, neg_x);

    // step2 : neg_one * neg_x = neg_one * (neg_one * x)
    let inner = d.imul(neg_one, x);
    let step2 = {
        let negx_eq = {
            let fwd = d.const_app(p.neg_one_mul, &[x]); // neg_one*x = neg x
            d.isymm(inner, neg_x, fwd)
        };
        d.icongr(neg_x, inner, negx_eq, &|d, y| d.imul(neg_one, y))
    };
    let mul_negone_inner = d.imul(neg_one, inner);

    // step3 : neg_one * (neg_one * x) = (neg_one * neg_one) * x
    let negone_sq = d.imul(neg_one, neg_one);
    let step3 = {
        let fwd = d.const_app(p.mul_assoc, &[neg_one, neg_one, x]);
        let lhs = d.imul(negone_sq, x);
        d.isymm(lhs, mul_negone_inner, fwd)
    };
    let negone_sq_x = d.imul(negone_sq, x);

    // negone_sq = one
    let negone_sq_eq_one = {
        let fwd = d.const_app(p.neg_one_mul, &[neg_one]); // negone_sq = neg neg_one
        let neg_neg_one = d.ineg(neg_one);
        // neg (neg one) = one, by rfl.
        let neg_neg_one_pf = d.irefl(one_c);
        d.itrans(negone_sq, neg_neg_one, one_c, fwd, neg_neg_one_pf)
    };

    // step5 : (neg_one*neg_one)*x = one*x
    let step5 = d.icongr(negone_sq, one_c, negone_sq_eq_one, &|d, y| d.imul(y, x));
    let one_x = d.imul(one_c, x);

    // step6 : one*x = x
    let step6 = d.const_app(p.one_mul, &[x]);

    let (_reached, chained) = d.ichain(
        neg_neg_x,
        &[
            (mul_negone_negx, step1),
            (mul_negone_inner, step2),
            (negone_sq_x, step3),
            (one_x, step5),
            (x, step6),
        ],
    );
    chained
}

/// `Eq Int ((neg a) * c) (neg (a*c))`, for any `a, c`.
pub(super) fn neg_mul(d: &mut IntDev<'_>, a: ExprId, c: ExprId) -> ExprId {
    let p = d.int();
    let one_c = d.ione();
    let neg_one = d.ineg(one_c);
    let neg_a = d.ineg(a);
    let ac = d.imul(a, c);
    let neg_ac = d.ineg(ac);
    let neg_a_c = d.imul(neg_a, c);

    // step1 : neg_a * c = (neg_one*a) * c
    let mul_negone_a = d.imul(neg_one, a);
    let step1 = {
        let a_eq = {
            let fwd = d.const_app(p.neg_one_mul, &[a]); // neg_one*a = neg a
            d.isymm(mul_negone_a, neg_a, fwd)
        };
        d.icongr(neg_a, mul_negone_a, a_eq, &|d, y| d.imul(y, c))
    };
    let mul_negone_a_c = d.imul(mul_negone_a, c);

    // step2 : (neg_one*a)*c = neg_one*(a*c)
    let step2 = d.const_app(p.mul_assoc, &[neg_one, a, c]);
    let neg_one_ac = d.imul(neg_one, ac);

    // step3 : neg_one*(a*c) = neg (a*c)
    let step3 = d.const_app(p.neg_one_mul, &[ac]);

    let (_reached, chained) = d.ichain(
        neg_a_c,
        &[
            (mul_negone_a_c, step1),
            (neg_one_ac, step2),
            (neg_ac, step3),
        ],
    );
    chained
}

/// `Eq Int (a * (neg c)) (neg (a*c))`, for any `a, c`.
fn mul_neg(d: &mut IntDev<'_>, a: ExprId, c: ExprId) -> ExprId {
    let p = d.int();
    let neg_c = d.ineg(c);
    let ac = d.imul(a, c);
    let ca = d.imul(c, a);
    let neg_ac = d.ineg(ac);
    let neg_ca = d.ineg(ca);
    let a_neg_c = d.imul(a, neg_c);
    let neg_c_a = d.imul(neg_c, a);

    // step1 : a * neg_c = neg_c * a
    let step1 = d.const_app(p.mul_comm, &[a, neg_c]);
    // step2 : neg_c * a = neg (c*a)
    let step2 = neg_mul(d, c, a);
    // step3 : neg (c*a) = neg (a*c)
    let step3 = {
        let comm = d.const_app(p.mul_comm, &[c, a]); // c*a = a*c
        d.icongr(ca, ac, comm, &|d, y| d.ineg(y))
    };
    let (_reached, chained) = d.ichain(
        a_neg_c,
        &[(neg_c_a, step1), (neg_ca, step2), (neg_ac, step3)],
    );
    chained
}

// ---------------------------------------------------------------------------
// Bézout's identity over `ℤ`.
// ---------------------------------------------------------------------------

/// Copy of `nat_prelude::bezout::bezout_elim`, generic over any [`NatOps`]
/// development (that private helper is scoped to `nat_prelude` and not
/// reachable from here). Eliminates a balanced Bézout certificate
/// `bezout m n g` into `target`, given a `minor` that receives the four
/// witnesses and the underlying equation.
fn bezout_elim<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    target: ExprId,
    certificate: ExprId,
    minor: &dyn Fn(&mut D, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_name = d.prelude().logic.exists_;
    let rec_name = d.prelude().logic.exists_rec;

    let mp_fv = d.fresh_fvar();
    let mp = d.kernel().fvar(mp_fv);
    let mn_fv = d.fresh_fvar();
    let mn = d.kernel().fvar(mn_fv);
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let nn_fv = d.fresh_fvar();
    let nn = d.kernel().fvar(nn_fv);

    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
    let nn_predicate = d.lam_fv(nn_fv, nat, equation);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let nn_exists = d.apply(exists, &[nat, nn_predicate]);
    let np_predicate = d.lam_fv(np_fv, nat, nn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let np_exists = d.apply(exists, &[nat, np_predicate]);
    let mn_predicate = d.lam_fv(mn_fv, nat, np_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mn_exists = d.apply(exists, &[nat, mn_predicate]);
    let mp_predicate = d.lam_fv(mp_fv, nat, mn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mp_exists = d.apply(exists, &[nat, mp_predicate]);

    let equation_fv = d.fresh_fvar();
    let equation_proof = d.kernel().fvar(equation_fv);
    let core = minor(d, mp, mn, np, nn, equation_proof);
    let nn_minor = {
        let with_equation = d.lam_fv(equation_fv, equation, core);
        d.lam_fv(nn_fv, nat, with_equation)
    };

    let np_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, nn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, nn_predicate, motive, nn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, nn_exists, eliminated);
        d.lam_fv(np_fv, nat, with_witness)
    };

    let mn_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, np_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, np_predicate, motive, np_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, np_exists, eliminated);
        d.lam_fv(mn_fv, nat, with_witness)
    };

    let mp_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, mn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, mn_predicate, motive, mn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, mn_exists, eliminated);
        d.lam_fv(mp_fv, nat, with_witness)
    };

    let motive = d.kernel().lam(anon, mp_exists, target, BinderInfo::Default);
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[nat, mp_predicate, motive, mp_minor, certificate])
}

/// Given `h : Eq Int ((x+q)+s) (bp+r)`, derive
/// `Eq Int x ((bp + neg q) + (r + neg s))`.
///
/// Pure abelian-group rearrangement: cancel `s` then `q` off the left via
/// `add_neg_cancel_right` twice, then re-associate the four-term sum with
/// `add_assoc`/`add_comm`.
fn ring_rearrange(
    d: &mut IntDev<'_>,
    x: ExprId,
    bp: ExprId,
    q: ExprId,
    r: ExprId,
    s: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let xq = d.iadd(x, q);
    let xqs = d.iadd(xq, s);
    let neg_s = d.ineg(s);
    let neg_q = d.ineg(q);
    let bpr = d.iadd(bp, r);

    // x = xq + neg_q, via two `add_neg_cancel_right` cancellations chained
    // through `h`.
    let xqs_negs = d.iadd(xqs, neg_s);
    let bpr_negs = d.iadd(bpr, neg_s);
    let eq_xq = {
        let cancel_s = d.const_app(p.add_neg_cancel_right, &[xq, s]); // (xq+s)+neg_s = xq
        let symm_cancel_s = d.isymm(xqs_negs, xq, cancel_s);
        let congr_h_s = d.icongr(xqs, bpr, h, &|d, y| d.iadd(y, neg_s));
        let (_reached, chained) = d.ichain(xq, &[(xqs_negs, symm_cancel_s), (bpr_negs, congr_h_s)]);
        chained
    };

    // l1 = (bpr + neg_s) + neg_q, with proof `eq_x_l1 : Eq Int x l1`.
    let xq_negq = d.iadd(xq, neg_q);
    let bpr_negs_negq = d.iadd(bpr_negs, neg_q);
    let (l1, eq_x_l1) = {
        let cancel_q = d.const_app(p.add_neg_cancel_right, &[x, q]); // (x+q)+neg_q = x
        let symm_cancel_q = d.isymm(xq_negq, x, cancel_q);
        let congr_eq_xq = d.icongr(xq, bpr_negs, eq_xq, &|d, y| d.iadd(y, neg_q));
        d.ichain(x, &[(xq_negq, symm_cancel_q), (bpr_negs_negq, congr_eq_xq)])
    };

    // Now reassociate `(bpr + neg_s) + neg_q` into `(bp+neg_q)+(r+neg_s)`.
    let bp_negq = d.iadd(bp, neg_q);
    let r_negs = d.iadd(r, neg_s);
    let target = d.iadd(bp_negq, r_negs);

    let reassoc = {
        // stepA : (bpr+neg_s)+neg_q = bpr+(neg_s+neg_q)
        let negs_negq = d.iadd(neg_s, neg_q);
        let negq_negs = d.iadd(neg_q, neg_s);
        let step_a = d.const_app(p.add_assoc, &[bpr, neg_s, neg_q]);
        let lhs0 = bpr_negs_negq;
        let rhs0 = d.iadd(bpr, negs_negq);

        // stepB : bpr+(neg_s+neg_q) = bpr+(neg_q+neg_s)
        let comm_sq = d.const_app(p.add_comm, &[neg_s, neg_q]);
        let step_b = d.icongr(negs_negq, negq_negs, comm_sq, &|d, y| d.iadd(bpr, y));
        let rhs1 = d.iadd(bpr, negq_negs);

        // stepC : bpr+(neg_q+neg_s) = (bpr+neg_q)+neg_s
        let bprq = d.iadd(bpr, neg_q);
        let bprq_negs = d.iadd(bprq, neg_s);
        let assoc_c_fwd = d.const_app(p.add_assoc, &[bpr, neg_q, neg_s]);
        let step_c = d.isymm(bprq_negs, rhs1, assoc_c_fwd);
        let rhs2 = bprq_negs;

        // stepD : bpr+neg_q = (bp+neg_q)+r
        let r_negq = d.iadd(r, neg_q);
        let negq_r = d.iadd(neg_q, r);
        let bp_r_negq = d.iadd(bp, r_negq);
        let bp_negq_r = d.iadd(bp, negq_r);
        let bp_negq_then_r = d.iadd(bp_negq, r);
        let step_d = {
            let d1 = d.const_app(p.add_assoc, &[bp, r, neg_q]); // (bp+r)+neg_q = bp+(r+neg_q)
            let comm_rq = d.const_app(p.add_comm, &[r, neg_q]); // r+neg_q = neg_q+r
            let d2 = d.icongr(r_negq, negq_r, comm_rq, &|d, y| d.iadd(bp, y));
            let d3_fwd = d.const_app(p.add_assoc, &[bp, neg_q, r]); // (bp+neg_q)+r = bp+(neg_q+r)
            let d3 = d.isymm(bp_negq_then_r, bp_negq_r, d3_fwd);
            let (_reached, chained) = d.ichain(
                bprq,
                &[(bp_r_negq, d1), (bp_negq_r, d2), (bp_negq_then_r, d3)],
            );
            chained
        };
        let step_d_congr = d.icongr(bprq, bp_negq_then_r, step_d, &|d, y| d.iadd(y, neg_s));
        let rhs3 = d.iadd(bp_negq_then_r, neg_s);

        // stepE : ((bp+neg_q)+r)+neg_s = (bp+neg_q)+(r+neg_s)
        let step_e = d.const_app(p.add_assoc, &[bp_negq, r, neg_s]);

        let (_reached, chained) = d.ichain(
            lhs0,
            &[
                (rhs0, step_a),
                (rhs1, step_b),
                (rhs2, step_c),
                (rhs3, step_d_congr),
                (target, step_e),
            ],
        );
        chained
    };

    d.itrans(x, l1, target, eq_x_l1, reassoc)
}

/// Given `x = A_i*mp_i + neg(A_i*mn_i)` folded into a product-sum shape,
/// factor `A_i` out: `Eq Int (bp+neg_q) (A_i * u0)` where `bp = A_i*mp_i`,
/// `q = A_i*mn_i`, `u0 = mp_i + neg mn_i`.
fn factor_out(d: &mut IntDev<'_>, big_a: ExprId, mp: ExprId, mn: ExprId) -> (ExprId, ExprId) {
    let p = d.int();
    let bp = d.imul(big_a, mp);
    let q = d.imul(big_a, mn);
    let neg_mn = d.ineg(mn);
    let u0 = d.iadd(mp, neg_mn);
    let neg_q = d.ineg(q);
    let bp_negq = d.iadd(bp, neg_q);
    let a_u0 = d.imul(big_a, u0);

    // neg_q = A_i * neg_mn
    let a_negmn = d.imul(big_a, neg_mn);
    let step_f1 = {
        let mn_eq = mul_neg(d, big_a, mn); // A_i*neg_mn = neg (A_i*mn) = neg q
        d.isymm(a_negmn, neg_q, mn_eq)
    };
    let step_f1_congr = d.icongr(neg_q, a_negmn, step_f1, &|d, y| d.iadd(bp, y));
    let rhs = d.iadd(bp, a_negmn);

    // bp + A_i*neg_mn = A_i*(mp+neg_mn) = A_i*u0
    let ld = d.const_app(p.left_distrib, &[big_a, mp, neg_mn]); // A_i*u0 = A_i*mp + A_i*neg_mn
    let step_f2 = d.isymm(a_u0, rhs, ld);

    let (_reached, chained) = d.ichain(bp_negq, &[(rhs, step_f1_congr), (a_u0, step_f2)]);
    (u0, chained)
}

/// `Or (Eq Int a (ofNat (natAbs a))) (Eq Int a (neg (ofNat (natAbs a))))`,
/// established by `Int.rec` case split on `a`: both branches close by `rfl`
/// (`ofNat (natAbs (ofNat n))` and `neg (ofNat (natAbs (negSucc n)))` both
/// reduce to the branch's own constructor term).
fn sign_cases(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let stmt = |d: &mut IntDev<'_>, args: &[ExprId]| {
        let a = args[0];
        let big_a = nat_abs(d, a);
        let of_a = d.of_nat(big_a);
        let neg_of_a = d.ineg(of_a);
        let left = d.ieq(a, of_a);
        let right = d.ieq(a, neg_of_a);
        d.or(left, right)
    };
    case_split(d, &[a], &stmt, &|d, branches: &[Branch]| {
        let (shape, field) = branches[0];
        match shape {
            Shape::OfNat => {
                let n = field;
                let of_n = d.of_nat(n);
                let big_of_n = nat_abs(d, of_n);
                let of_big = d.of_nat(big_of_n);
                let neg_of_big = d.ineg(of_big);
                let refl = d.irefl(of_n);
                let left = d.ieq(of_n, of_big);
                let right = d.ieq(of_n, neg_of_big);
                d.or_inl(left, right, refl)
            }
            Shape::NegSucc => {
                let n = field;
                let neg_succ_n = d.neg_succ(n);
                let big = nat_abs(d, neg_succ_n);
                let of_big = d.of_nat(big);
                let neg_of_big = d.ineg(of_big);
                let refl = d.irefl(neg_succ_n);
                let left = d.ieq(neg_succ_n, of_big);
                let right = d.ieq(neg_succ_n, neg_of_big);
                d.or_inr(left, right, refl)
            }
        }
    })
}

/// `fun (u : Int) => Eq Int (a*u) rhs` — the predicate an `Int`-quantified
/// "some scaling of `a` reaches `rhs`" existential quantifies.
fn au_pred(d: &mut IntDev<'_>, a: ExprId, rhs: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let au = d.imul(a, u);
    let body = d.ieq(au, rhs);
    d.lam_fv(u_fv, int_ty, body)
}

/// Eliminate `witness : Exists Int predicate` into `target`, given
/// `minor : ∀ (u : Int), predicate u → target`. The `Int`-quantified
/// counterpart of `exists_elim` (which is fixed to `Nat`-quantified
/// existentials).
fn int_exists_elim(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_ty = {
        let name = d.int().logic.exists_;
        let e = d.kernel().const_(name, vec![one]);
        d.apply(e, &[int_ty, predicate])
    };
    let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, predicate, motive, minor, witness])
}

/// From `h1 : Eq Int x1 y1` and `h2 : Eq Int x2 y2`, derive
/// `Eq Int (x1+x2) (y1+y2)`.
fn iadd_congr2(
    d: &mut IntDev<'_>,
    x1: ExprId,
    y1: ExprId,
    h1: ExprId,
    x2: ExprId,
    y2: ExprId,
    h2: ExprId,
) -> ExprId {
    let step1 = d.icongr(x1, y1, h1, &|d, y| d.iadd(y, x2));
    let step2 = d.icongr(x2, y2, h2, &|d, y| d.iadd(y1, y));
    let x1x2 = d.iadd(x1, x2);
    let y1x2 = d.iadd(y1, x2);
    let y1y2 = d.iadd(y1, y2);
    d.itrans(x1x2, y1x2, y1y2, step1, step2)
}

/// Given `disj : Or (Eq Int a big_a_cast) (Eq Int a (neg big_a_cast))`,
/// produce a proof of `∃ (u : Int), Eq Int (a*u) (big_a_cast*u0)`.
///
/// `u := u0` on the left branch (direct congruence); `u := neg u0` on the
/// right, where `a*(neg u0) = (neg big_a_cast)*(neg u0) = big_a_cast*u0` by
/// `neg_mul`/`mul_neg`/`neg_neg`.
fn match_sign(
    d: &mut IntDev<'_>,
    a: ExprId,
    big_a_cast: ExprId,
    u0: ExprId,
    disj: ExprId,
) -> ExprId {
    let neg_big_a = d.ineg(big_a_cast);
    let left_ty = d.ieq(a, big_a_cast);
    let right_ty = d.ieq(a, neg_big_a);
    let neg_u0 = d.ineg(u0);
    let rhs = d.imul(big_a_cast, u0);
    let predicate = au_pred(d, a, rhs);
    let int_ty = d.int_ty();
    let one = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let exists_ty = {
        let name = d.int().logic.exists_;
        let e = d.kernel().const_(name, vec![one]);
        d.apply(e, &[int_ty, predicate])
    };

    let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let proof = d.icongr(a, big_a_cast, h, &|d, y| d.imul(y, u0));
        let intro = d.kernel().const_(intro_name, vec![one]);
        d.apply(intro, &[int_ty, predicate, u0, proof])
    };
    let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let a_negu0 = d.imul(a, neg_u0);
        let negbiga_negu0 = d.imul(neg_big_a, neg_u0);
        let biga_negu0 = d.imul(big_a_cast, neg_u0);
        let biga_u0 = d.imul(big_a_cast, u0);
        let neg_biga_u0 = d.ineg(biga_u0);
        let neg_neg_biga_u0 = d.ineg(neg_biga_u0);

        let step1 = d.icongr(a, neg_big_a, h, &|d, y| d.imul(y, neg_u0));
        let step2 = neg_mul(d, big_a_cast, neg_u0); // negbiga_negu0 = neg biga_negu0
        let step3 = mul_neg(d, big_a_cast, u0); // biga_negu0 = neg biga_u0
        let step3_congr = d.icongr(biga_negu0, neg_biga_u0, step3, &|d, y| d.ineg(y));
        let step4 = neg_neg(d, biga_u0); // neg (neg biga_u0) = biga_u0
        let neg_biga_negu0 = d.ineg(biga_negu0);
        let (_reached, chained) = d.ichain(
            a_negu0,
            &[
                (negbiga_negu0, step1),
                (neg_biga_negu0, step2),
                (neg_neg_biga_u0, step3_congr),
                (rhs, step4),
            ],
        );
        let intro = d.kernel().const_(intro_name, vec![one]);
        d.apply(intro, &[int_ty, predicate, neg_u0, chained])
    };
    d.or_elim(left_ty, right_ty, exists_ty, disj, on_left, on_right)
}

/// `gcd_eq_gcd_ab : ∀ (a b : Int), ∃ (u v : Int),
/// Eq Int (ofNat (gcd a b)) (a*u + b*v)` — Bézout's identity over `ℤ`
/// (Elements VII.2, strong form).
///
/// Transports `Nat.gcd_bezout`'s balanced witnesses `(mp, mn, np, nn)`
/// (`g + A*mn + B*nn = A*mp + B*np` over `A = natAbs a`, `B = natAbs b`)
/// through the cast: casting commutes with `+`/`*` on `ofNat`-wrapped terms by
/// pure computation, so the Nat equation lifts directly to
/// `ofNat g = (A_i*mp_i + neg (A_i*mn_i)) + (B_i*np_i + neg (B_i*nn_i))`
/// ([`ring_rearrange`]), which factors as `A_i*u0 + B_i*v0` for
/// `u0 = mp_i + neg mn_i`, `v0 = np_i + neg nn_i` ([`factor_out`]). That much
/// needs no sign information about `a, b` at all — only their magnitudes.
///
/// The one place sign matters: `A_i = ofNat (natAbs a)` equals `a` when
/// `a ≥ 0`, but `neg a` when `a < 0` ([`sign_cases`]); [`match_sign`] absorbs
/// that flip into the choice of `u` (`u0` or `neg u0`), symmetrically for `v`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_gcd_eq_gcd_ab(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_eq_gcd_ab, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let big_a = nat_abs(d, a);
        let big_b = nat_abs(d, b);
        let g = NatOps::gcd(d, big_a, big_b);
        let x = d.of_nat(g);
        let a_i = d.of_nat(big_a);
        let b_i = d.of_nat(big_b);

        // The final statement: ∃ u v : Int, Eq Int (ofNat (gcd a b)) (a*u+b*v).
        let int_ty = d.int_ty();
        let one = d.level_one();
        let inner_pred_for = |d: &mut IntDev<'_>, u: ExprId| -> ExprId {
            let v_fv = d.fresh_fvar();
            let vv = d.kernel().fvar(v_fv);
            let au = d.imul(a, u);
            let bv = d.imul(b, vv);
            let sum = d.iadd(au, bv);
            let body = d.ieq(x, sum);
            d.lam_fv(v_fv, int_ty, body)
        };
        let exists_name = d.int().logic.exists_;
        let outer_pred = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let body = {
                let inner_pred = inner_pred_for(d, u);
                let exists = d.kernel().const_(exists_name, vec![one]);
                d.apply(exists, &[int_ty, inner_pred])
            };
            d.lam_fv(u_fv, int_ty, body)
        };
        let stmt = {
            let exists = d.kernel().const_(exists_name, vec![one]);
            d.apply(exists, &[int_ty, outer_pred])
        };

        // The Bézout certificate over the magnitudes.
        let certificate = d.lemma(p.nat.gcd_bezout, &[big_a, big_b]);

        let sign_a = sign_cases(d, a);
        let sign_b = sign_cases(d, b);

        let minor = &|d: &mut IntDev<'_>,
                      mp: ExprId,
                      mn: ExprId,
                      np: ExprId,
                      nn: ExprId,
                      eqn: ExprId|
         -> ExprId {
            let mp_i = d.of_nat(mp);
            let mn_i = d.of_nat(mn);
            let np_i = d.of_nat(np);
            let nn_i = d.of_nat(nn);

            let m_neg = NatOps::mul(d, big_a, mn);
            let n_neg = NatOps::mul(d, big_b, nn);
            let g_plus = NatOps::add(d, g, m_neg);
            let left_nat = NatOps::add(d, g_plus, n_neg);
            let m_pos = NatOps::mul(d, big_a, mp);
            let n_pos = NatOps::mul(d, big_b, np);
            let right_nat = NatOps::add(d, m_pos, n_pos);
            let cast_eq = d.nat_eq_to_int(left_nat, right_nat, eqn, &|d, y| d.of_nat(y));

            let bp = d.imul(a_i, mp_i);
            let q = d.imul(a_i, mn_i);
            let r = d.imul(b_i, np_i);
            let s = d.imul(b_i, nn_i);
            let rearranged = ring_rearrange(d, x, bp, q, r, s, cast_eq);

            let (u0, bp_negq_eq) = factor_out(d, a_i, mp_i, mn_i);
            let (v0, r_negs_eq) = factor_out(d, b_i, np_i, nn_i);
            let neg_q = d.ineg(q);
            let neg_s = d.ineg(s);
            let bp_negq = d.iadd(bp, neg_q);
            let r_negs = d.iadd(r, neg_s);
            let a_u0 = d.imul(a_i, u0);
            let b_v0 = d.imul(b_i, v0);
            let sum_eq = iadd_congr2(d, bp_negq, a_u0, bp_negq_eq, r_negs, b_v0, r_negs_eq);
            let sum = d.iadd(bp_negq, r_negs);

            let match_a = match_sign(d, a, a_i, u0, sign_a);
            let match_b = match_sign(d, b, b_i, v0, sign_b);
            let pred_a = au_pred(d, a, a_u0);
            let pred_b = au_pred(d, b, b_v0);

            // Nested elimination: bind `u`/`proof_au` (from `match_a`), then
            // `v`/`proof_bv` (from `match_b`), and close with `coreeq`.
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let pau_fv = d.fresh_fvar();
            let proof_au = d.kernel().fvar(pau_fv);
            let au = d.imul(a, u);
            let proof_au_ty = d.ieq(au, a_u0);

            let vv_fv = d.fresh_fvar();
            let vv = d.kernel().fvar(vv_fv);
            let pbv_fv = d.fresh_fvar();
            let proof_bv = d.kernel().fvar(pbv_fv);
            let bv = d.imul(b, vv);
            let proof_bv_ty = d.ieq(bv, b_v0);

            let sum2 = d.iadd(au, bv);
            let a_u0_b_v0 = d.iadd(a_u0, b_v0);
            let eq2 = iadd_congr2(d, au, a_u0, proof_au, bv, b_v0, proof_bv);
            let symm_eq2 = d.isymm(sum2, a_u0_b_v0, eq2);
            let sum_to_sum2 = d.itrans(sum, a_u0_b_v0, sum2, sum_eq, symm_eq2);
            let final_eq = d.itrans(x, sum, sum2, rearranged, sum_to_sum2);

            let inner_exists_witness = vv;
            let inner_pred = inner_pred_for(d, u);
            let inner_proof = {
                let intro_name = d.int().logic.exists_intro;
                let intro = d.kernel().const_(intro_name, vec![one]);
                d.apply(intro, &[int_ty, inner_pred, inner_exists_witness, final_eq])
            };
            let minor_b = d.lam_fv(pbv_fv, proof_bv_ty, inner_proof);
            let minor_b = d.lam_fv(vv_fv, int_ty, minor_b);
            // Target for eliminating `match_b`: `∃v, Eq x (a*u+b*v)`, the
            // INNER existential only — `u` is still a fixed local variable at
            // this point, not yet eliminated.
            let inner_exists_ty = {
                let exists = d.kernel().const_(exists_name, vec![one]);
                d.apply(exists, &[int_ty, inner_pred])
            };
            let eliminated_b = int_exists_elim(d, pred_b, inner_exists_ty, match_b, minor_b);
            // Now wrap with the OUTER `Exists.intro` for `u` to reach `stmt`
            // (`∃u,∃v, ...`) *before* abstracting `u` away — the elimination of
            // `match_a` needs its `minor`'s conclusion to be `stmt` itself,
            // which does not mention `u`.
            let outer_intro = {
                let intro_name = d.int().logic.exists_intro;
                let intro = d.kernel().const_(intro_name, vec![one]);
                d.apply(intro, &[int_ty, outer_pred, u, eliminated_b])
            };
            let with_pau = d.lam_fv(pau_fv, proof_au_ty, outer_intro);
            let minor_a = d.lam_fv(u_fv, int_ty, with_pau);
            int_exists_elim(d, pred_a, stmt, match_a, minor_a)
        };

        let proof = bezout_elim(d, big_a, big_b, g, stmt, certificate, minor);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.Coprime`, Gauss's lemma, and Euclid's lemma (Elements VII.30) — the
// converse of Bézout and its two corollaries.
// ---------------------------------------------------------------------------

/// Admit `Int.Coprime : Int → Int → Prop := fun a b => Eq Nat (gcd a b) 1`.
///
/// The converse of Bézout's identity ([`declare_gcd_eq_gcd_ab`]):
/// [`declare_coprime_of_bezout_one`] proves the direction *from* a Bézout
/// certificate, and [`declare_gauss_lemma`] is the one place this development
/// actually needs the predicate rather than the bare equation.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_coprime(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let prop = d.kernel().sort_zero();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let g = igcd(d, a, b);
    let one_nat = d.num(1);
    let body = d.eq(g, one_nat);
    let value = {
        let inner = d.lam_fv(b_fv, int_ty, body);
        d.lam_fv(a_fv, int_ty, inner)
    };
    let ty = {
        let inner = d.arrow(int_ty, prop);
        d.arrow(int_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.coprime,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// `coprime_of_bezout_one : ∀ (a b u v : Int), Eq Int (a*u+b*v) one → Coprime a b`.
///
/// The converse of [`declare_gcd_eq_gcd_ab`]: `ofNat (gcd a b)` divides both
/// `a` and `b`, hence both `a*u` and `b*v`, hence their sum; given that sum is
/// `Int.one`, [`declare_nat_abs_dvd_nat_abs_of_dvd`] carries
/// `ofNat (gcd a b) ∣ one` down to `Nat.dvd (gcd a b) 1` (both `natAbs`
/// computations are `rfl`), and `Nat.eq_one_of_dvd_one` closes it.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_coprime_of_bezout_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.coprime_of_bezout_one, 4, &|d, v| {
        let (a, b, u, vv) = (v[0], v[1], v[2], v[3]);
        let au = d.imul(a, u);
        let bv = d.imul(b, vv);
        let sum = d.iadd(au, bv);
        let one_i = d.ione();
        let hyp_ty = d.ieq(sum, one_i);
        let g = igcd(d, a, b);
        let goal = d.const_app(p.coprime, &[a, b]);
        let stmt = d.arrow(hyp_ty, goal);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let g_i = d.of_nat(g);
        let dvd_a = d.const_app(p.gcd_dvd_left, &[a, b]);
        let dvd_b = d.const_app(p.gcd_dvd_right, &[a, b]);

        let dvd_au = {
            let step = d.const_app(p.dvd_mul_right, &[a, u]);
            d.const_app(p.dvd_trans, &[g_i, a, au, dvd_a, step])
        };
        let dvd_bv = {
            let step = d.const_app(p.dvd_mul_right, &[b, vv]);
            d.const_app(p.dvd_trans, &[g_i, b, bv, dvd_b, step])
        };
        let dvd_sum = d.const_app(p.dvd_add, &[g_i, au, bv, dvd_au, dvd_bv]);
        let dvd_one = {
            let motive = |d: &mut IntDev<'_>, x: ExprId| idvd(d, g_i, x);
            d.int_eq_rewrite(sum, one_i, h, dvd_sum, &motive)
        };
        let nat_dvd_one = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[g_i, one_i, dvd_one]);
        let proof_body = d.lemma(p.nat.eq_one_of_dvd_one, &[g, nat_dvd_one]);
        let proof = d.lam_fv(h_fv, hyp_ty, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// Given `eq_one_sum : Eq Int one_i (a*u+b*v)`, derive
/// `(a_cu, bc_v, Eq Int c (a_cu + bc_v))` where `a_cu = a*(c*u)` and
/// `bc_v = (b*c)*v` — the shape [`declare_gauss_lemma`] needs to close with
/// `dvd_mul_right`/`dvd_trans`/`dvd_add` alone.
///
/// Pure ring rearrangement: `c = c*1 = c*(a*u+b*v) = c*(a*u) + c*(b*v)`, and
/// each summand is re-associated/commuted into the target shape by
/// `mul_assoc`/`mul_comm` alone — no case split, unlike the Bézout
/// development this composes with.
fn gauss_rearrange(
    d: &mut IntDev<'_>,
    c: ExprId,
    a: ExprId,
    u: ExprId,
    b: ExprId,
    v: ExprId,
    eq_one_sum: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let p = d.int();
    let one_i = d.ione();
    let au = d.imul(a, u);
    let bv = d.imul(b, v);
    let sum_uv = d.iadd(au, bv);

    // c = c*one_i
    let c_one = d.imul(c, one_i);
    let step1 = {
        let fwd = d.const_app(p.mul_one, &[c]); // c*one = c
        d.isymm(c_one, c, fwd)
    };

    // c*one_i = c*sum_uv
    let c_sum = d.imul(c, sum_uv);
    let step2 = d.icongr(one_i, sum_uv, eq_one_sum, &|d, y| d.imul(c, y));

    // c*sum_uv = c*au + c*bv
    let c_au = d.imul(c, au);
    let c_bv = d.imul(c, bv);
    let step3 = d.const_app(p.left_distrib, &[c, au, bv]);
    let c_au_c_bv = d.iadd(c_au, c_bv);

    // c*au = a*(c*u)
    let ca = d.imul(c, a);
    let ca_u = d.imul(ca, u);
    let step4a = {
        let fwd = d.const_app(p.mul_assoc, &[c, a, u]); // (c*a)*u = c*(a*u)
        d.isymm(ca_u, c_au, fwd)
    };
    let ac = d.imul(a, c);
    let ac_u = d.imul(ac, u);
    let step4b = {
        let comm = d.const_app(p.mul_comm, &[c, a]); // c*a = a*c
        d.icongr(ca, ac, comm, &|d, y| d.imul(y, u))
    };
    let cu = d.imul(c, u);
    let a_cu = d.imul(a, cu);
    let step4c = d.const_app(p.mul_assoc, &[a, c, u]); // (a*c)*u = a*(c*u)
    let (_reached4, chain4) = d.ichain(c_au, &[(ca_u, step4a), (ac_u, step4b), (a_cu, step4c)]);

    // c*bv = (b*c)*v
    let cb = d.imul(c, b);
    let cb_v = d.imul(cb, v);
    let step5a = {
        let fwd = d.const_app(p.mul_assoc, &[c, b, v]); // (c*b)*v = c*(b*v)
        d.isymm(cb_v, c_bv, fwd)
    };
    let bc = d.imul(b, c);
    let bc_v = d.imul(bc, v);
    let step5b = {
        let comm = d.const_app(p.mul_comm, &[c, b]); // c*b = b*c
        d.icongr(cb, bc, comm, &|d, y| d.imul(y, v))
    };
    let (_reached5, chain5) = d.ichain(c_bv, &[(cb_v, step5a), (bc_v, step5b)]);

    let target = d.iadd(a_cu, bc_v);
    let combine = iadd_congr2(d, c_au, a_cu, chain4, c_bv, bc_v, chain5);

    let (_final_target, final_chain) = d.ichain(
        c,
        &[
            (c_one, step1),
            (c_sum, step2),
            (c_au_c_bv, step3),
            (target, combine),
        ],
    );
    (a_cu, bc_v, final_chain)
}

/// `gauss_lemma : ∀ (a b c : Int), Coprime a b → a ∣ (b*c) → a ∣ c` —
/// Elements VII.30's engine.
///
/// The Bézout route: from `1 = a*u + b*v` (the coprimality certificate),
/// `c = a*(c*u) + (b*c)*v` ([`gauss_rearrange`]), and both summands are
/// divisible by `a` — the first outright (`dvd_mul_right`), the second
/// through the hypothesis (`dvd_trans` with `dvd_mul_right (b*c) v`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_gauss_lemma(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gauss_lemma, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let coprime_ty = d.const_app(p.coprime, &[a, b]);
        let bc = d.imul(b, c);
        let hyp2_ty = idvd(d, a, bc);
        let goal = idvd(d, a, c);
        let stmt = {
            let inner = d.arrow(hyp2_ty, goal);
            d.arrow(coprime_ty, inner)
        };

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        // `g` is built exactly as `gcd_eq_gcd_ab`'s own Bézout certificate
        // builds it, so `bez`'s real predicate below matches ours by
        // construction rather than by an appeal to deep defeq.
        let big_a = nat_abs(d, a);
        let big_b = nat_abs(d, b);
        let g = NatOps::gcd(d, big_a, big_b);
        let one_nat = d.num(1);
        let g_i = d.of_nat(g);
        let one_i = d.ione();

        // `h1 : Coprime a b`, used directly at its unfolded type `Eq Nat g 1`.
        let cast_eq = d.nat_eq_to_int(g, one_nat, h1, &|d, x| d.of_nat(x));

        // The Bézout certificate for this exact `g`.
        let bez = d.const_app(p.gcd_eq_gcd_ab, &[a, b]);

        let int_ty = d.int_ty();
        let one_level = d.level_one();
        let exists_name = d.int().logic.exists_;
        let inner_pred_for = |d: &mut IntDev<'_>, u: ExprId| -> ExprId {
            let vv_fv = d.fresh_fvar();
            let vv = d.kernel().fvar(vv_fv);
            let au = d.imul(a, u);
            let bv = d.imul(b, vv);
            let sum = d.iadd(au, bv);
            let body = d.ieq(g_i, sum);
            d.lam_fv(vv_fv, int_ty, body)
        };
        let outer_pred = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_pred = inner_pred_for(d, u);
            let exists = d.kernel().const_(exists_name, vec![one_level]);
            let body = d.apply(exists, &[int_ty, inner_pred]);
            d.lam_fv(u_fv, int_ty, body)
        };

        let minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_pred = inner_pred_for(d, u);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let ha_ty = {
                let exists = d.kernel().const_(exists_name, vec![one_level]);
                d.apply(exists, &[int_ty, inner_pred])
            };

            let inner_minor = {
                let vv_fv = d.fresh_fvar();
                let vv = d.kernel().fvar(vv_fv);
                let au = d.imul(a, u);
                let bv = d.imul(b, vv);
                let sum = d.iadd(au, bv);
                let eq_ty = d.ieq(g_i, sum);
                let eq_fv = d.fresh_fvar();
                let eq_h = d.kernel().fvar(eq_fv);

                let one_eq_sum = {
                    let rev = d.isymm(g_i, one_i, cast_eq);
                    d.itrans(one_i, g_i, sum, rev, eq_h)
                };
                let (a_cu, bc_v, chain_eq) = gauss_rearrange(d, c, a, u, b, vv, one_eq_sum);
                let target = d.iadd(a_cu, bc_v);

                let dvd_a_cu = {
                    let cu = d.imul(c, u);
                    d.const_app(p.dvd_mul_right, &[a, cu])
                };
                let dvd_bc_v = {
                    let bcv = d.imul(bc, vv);
                    let step = d.const_app(p.dvd_mul_right, &[bc, vv]);
                    d.const_app(p.dvd_trans, &[a, bc, bcv, h2, step])
                };
                let dvd_target = d.const_app(p.dvd_add, &[a, a_cu, bc_v, dvd_a_cu, dvd_bc_v]);
                let rev_chain = d.isymm(c, target, chain_eq);
                let motive = |d: &mut IntDev<'_>, x: ExprId| idvd(d, a, x);
                let body = d.int_eq_rewrite(target, c, rev_chain, dvd_target, &motive);

                let with_eq = d.lam_fv(eq_fv, eq_ty, body);
                d.lam_fv(vv_fv, int_ty, with_eq)
            };
            let eliminated = int_exists_elim(d, inner_pred, goal, ha, inner_minor);
            let with_ha = d.lam_fv(ha_fv, ha_ty, eliminated);
            d.lam_fv(u_fv, int_ty, with_ha)
        };

        let disjunction_result = int_exists_elim(d, outer_pred, goal, bez, minor);
        let with_h2 = d.lam_fv(h2_fv, hyp2_ty, disjunction_result);
        let proof = d.lam_fv(h1_fv, coprime_ty, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.dvd_of_dvd_mul_right_of_gcd_one : ∀ a b c,
/// a ∣ (b*c) → Eq Nat (gcd a b) 1 → a ∣ c` — Mathlib v4.30 verbatim.
///
/// Exactly [`declare_gauss_lemma`]'s statement with its two hypotheses
/// reordered (dvd first, gcd-equation second, matching Mathlib's argument
/// order): `Eq Nat (gcd a b) 1` is `Coprime a b` unfolded one `Definition`
/// step, so it type-checks directly where [`gauss_lemma`](IntPrelude::gauss_lemma)
/// expects a `Coprime a b` proof.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_dvd_of_dvd_mul_right_of_gcd_one(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_of_dvd_mul_right_of_gcd_one, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let bc = d.imul(b, c);
        let hyp1_ty = idvd(d, a, bc);
        let g_ab = igcd(d, a, b);
        let one_nat = d.num(1);
        let hyp2_ty = d.eq(g_ab, one_nat);
        let goal = idvd(d, a, c);
        let stmt = {
            let inner = d.arrow(hyp2_ty, goal);
            d.arrow(hyp1_ty, inner)
        };

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let result = d.const_app(p.gauss_lemma, &[a, b, c, h2, h1]);
        let with_h2 = d.lam_fv(h2_fv, hyp2_ty, result);
        let proof = d.lam_fv(h1_fv, hyp1_ty, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.dvd_of_dvd_mul_left_of_gcd_one : ∀ a b c,
/// a ∣ (b*c) → Eq Nat (gcd a c) 1 → a ∣ b` — Mathlib v4.30 verbatim.
///
/// [`declare_gauss_lemma`] applied at `(a, c, b)` needs `a ∣ (c*b)`, not the
/// given `a ∣ (b*c)`; the two witnesses differ by `Int.mul_comm b c`, so the
/// hypothesis is eliminated and its equation rewritten before re-introducing
/// the divisibility, exactly the pattern [`declare_dvd_mul_left`] uses for
/// `a ∣ (b*a)` from `a ∣ (a*b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_dvd_of_dvd_mul_left_of_gcd_one(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_of_dvd_mul_left_of_gcd_one, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let bc = d.imul(b, c);
        let cb = d.imul(c, b);
        let hyp1_ty = idvd(d, a, bc);
        let g_ac = igcd(d, a, c);
        let one_nat = d.num(1);
        let hyp2_ty = d.eq(g_ac, one_nat);
        let goal = idvd(d, a, b);
        let stmt = {
            let inner = d.arrow(hyp2_ty, goal);
            d.arrow(hyp1_ty, inner)
        };

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let int_ty = d.int_ty();
        let target = idvd(d, a, cb);
        let dvd_a_cb = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let ak = d.imul(a, k);
            let eq_ty = d.ieq(bc, ak);
            let eq_fv = d.fresh_fvar();
            let eq_h = d.kernel().fvar(eq_fv);

            let mc = {
                let name = d.int().mul_comm;
                d.const_app(name, &[b, c])
            };
            let rev = d.isymm(bc, cb, mc);
            let rewritten = d.itrans(cb, bc, ak, rev, eq_h);
            let intro_proof = idvd_intro(d, a, cb, k, rewritten);
            let with_eq = d.lam_fv(eq_fv, eq_ty, intro_proof);
            let minor = d.lam_fv(k_fv, int_ty, with_eq);
            idvd_elim(d, a, bc, target, h1, minor)
        };

        let result = d.const_app(p.gauss_lemma, &[a, c, b, h2, dvd_a_cb]);
        let with_h2 = d.lam_fv(h2_fv, hyp2_ty, result);
        let proof = d.lam_fv(h1_fv, hyp1_ty, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.gcd_greatest : ∀ a b d, 0 ≤ d → d ∣ a → d ∣ b →
/// (∀ e, e ∣ a → e ∣ b → e ∣ d) → Eq Int d (ofNat (gcd a b))` — Mathlib v4.30
/// verbatim.
///
/// Both `Int.dvd` directions come from the universal property already proved:
/// `d ∣ ofNat (gcd a b)` is [`declare_dvd_gcd`] fed `d`'s own two hypotheses
/// directly (`c := d`), and `ofNat (gcd a b) ∣ d` is the fact's own universal
/// hypothesis fed [`declare_gcd_dvd_left_right`]'s two lemmas (`e := ofNat
/// (gcd a b)`). Mutual `Int.dvd` transports to mutual `Nat.dvd` between
/// `natAbs d` and `gcd a b` via [`declare_nat_abs_dvd_nat_abs_of_dvd`]
/// (`natAbs (ofNat n)` reduces to `n` by `rfl`, exactly as in
/// [`declare_gcd_dvd_left_right`]'s own comment), [`nat_dvd_antisymm`] gives
/// `Eq Nat (natAbs d) (gcd a b)`, and `0 ≤ d` (via
/// [`Self::of_nat_nat_abs_of_nonneg`] — accessed through `p`, not `Self`)
/// lifts `d = ofNat (natAbs d)` to close the chain.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_gcd_greatest(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_greatest, 3, &|d, v| {
        let (a, b, dd) = (v[0], v[1], v[2]);
        let int_ty = d.int_ty();
        let zero = d.izero();
        let nonneg_ty = d.ile(zero, dd);
        let dvd_a_ty = idvd(d, dd, a);
        let dvd_b_ty = idvd(d, dd, b);

        let g = igcd(d, a, b);
        let of_g = d.of_nat(g);

        let universal_ty = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let e_dvd_a = idvd(d, e, a);
            let e_dvd_b = idvd(d, e, b);
            let e_dvd_d = idvd(d, e, dd);
            let inner = d.arrow(e_dvd_b, e_dvd_d);
            let body = d.arrow(e_dvd_a, inner);
            d.pi_fv(e_fv, int_ty, body)
        };

        let goal = d.ieq(dd, of_g);
        let stmt = {
            let inner3 = d.arrow(universal_ty, goal);
            let inner2 = d.arrow(dvd_b_ty, inner3);
            let inner1 = d.arrow(dvd_a_ty, inner2);
            d.arrow(nonneg_ty, inner1)
        };

        let nonneg_fv = d.fresh_fvar();
        let nonneg = d.kernel().fvar(nonneg_fv);
        let dvd_a_fv = d.fresh_fvar();
        let dvd_a = d.kernel().fvar(dvd_a_fv);
        let dvd_b_fv = d.fresh_fvar();
        let dvd_b = d.kernel().fvar(dvd_b_fv);
        let univ_fv = d.fresh_fvar();
        let univ = d.kernel().fvar(univ_fv);

        // `d ∣ ofNat (gcd a b)`, straight from `dvd_gcd` fed `d`'s own hyps.
        let d_dvd_g = d.const_app(p.dvd_gcd, &[dd, a, b, dvd_a, dvd_b]);

        // `ofNat (gcd a b) ∣ d`, from the universal hypothesis at `e := ofNat (gcd a b)`.
        let g_dvd_a = d.const_app(p.gcd_dvd_left, &[a, b]);
        let g_dvd_b = d.const_app(p.gcd_dvd_right, &[a, b]);
        let g_dvd_d = d.apply(univ, &[of_g, g_dvd_a, g_dvd_b]);

        // Transport both to `Nat.dvd`: `natAbs (ofNat (gcd a b))` reduces to
        // `gcd a b` by `rfl`, so these type-check directly at the `Nat`-level
        // shapes `nat_dvd_antisymm` needs.
        let natabs_d = nat_abs(d, dd);
        let n_forward = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[dd, of_g, d_dvd_g]);
        let n_backward = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_g, dd, g_dvd_d]);
        let nat_eq = nat_dvd_antisymm(d, natabs_d, g, n_forward, n_backward);

        // `d = ofNat (natAbs d)` from `0 ≤ d`, then cast the `Nat` equation up.
        let of_natabs_d = d.of_nat(natabs_d);
        let d_eq_ofnat_natabs = d.const_app(p.of_nat_nat_abs_of_nonneg, &[dd, nonneg]);
        let flipped = d.isymm(of_natabs_d, dd, d_eq_ofnat_natabs);
        let cast_up = d.nat_eq_to_int(natabs_d, g, nat_eq, &|d, x| d.of_nat(x));
        let proof_body = d.itrans(dd, of_natabs_d, of_g, flipped, cast_up);

        let with_univ = d.lam_fv(univ_fv, universal_ty, proof_body);
        let with_dvd_b = d.lam_fv(dvd_b_fv, dvd_b_ty, with_univ);
        let with_dvd_a = d.lam_fv(dvd_a_fv, dvd_a_ty, with_dvd_b);
        let proof = d.lam_fv(nonneg_fv, nonneg_ty, with_dvd_a);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.modEq_inverse_exists :
/// ∀ n a, 0 < n → Coprime a n → ∃ b, ModEq n (a*b) one` — the modular
/// inverse.
///
/// Direct from Bézout ([`declare_gcd_eq_gcd_ab`]): `Coprime a n` casts the
/// certificate's `ofNat (gcd a n)` down to `one`, giving `one = a*u + n*v`
/// for the witnesses `u, v` the certificate supplies. `u` IS the inverse:
/// commuting the sum and applying `add_neg_cancel_right` gives
/// `one - a*u = n*v`, i.e. `n ∣ (one - a*u)` with witness `v` — exactly the
/// divisibility `modEq_iff_dvd` needs for `ModEq n (a*u) one`.
///
/// `g` is built exactly as `gcd_eq_gcd_ab`'s own certificate builds it (the
/// same reasoning [`declare_gauss_lemma`]'s doc comment spells out), so the
/// predicate below lines up with `bez`'s by construction rather than by an
/// appeal to deep defeq.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_modeq_inverse_exists(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_inverse_exists, 2, &|d, v| {
        let (n, a) = (v[0], v[1]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let coprime_ty = d.const_app(p.coprime, &[a, n]);
        let int_ty = d.int_ty();
        let one_level = d.level_one();
        let one_i = d.ione();

        let goal_pred = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let ab = d.imul(a, b);
            let body = super::modeq::imodeq(d, n, ab, one_i);
            d.lam_fv(b_fv, int_ty, body)
        };
        let exists_name = d.int().logic.exists_;
        let goal = {
            let exists = d.kernel().const_(exists_name, vec![one_level]);
            d.apply(exists, &[int_ty, goal_pred])
        };

        let inner_arrow = d.arrow(coprime_ty, goal);
        let stmt = d.arrow(pos_ty, inner_arrow);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);

        // `g` built exactly as `gcd_eq_gcd_ab`'s own certificate builds it.
        let big_a = nat_abs(d, a);
        let big_n = nat_abs(d, n);
        let g = NatOps::gcd(d, big_a, big_n);
        let g_i = d.of_nat(g);
        let one_nat = d.num(1);
        // `h1 : Coprime a n`, used directly at its unfolded type `Eq Nat g 1`.
        let cast_eq = d.nat_eq_to_int(g, one_nat, h1, &|d, x| d.of_nat(x));

        let bez = d.const_app(p.gcd_eq_gcd_ab, &[a, n]);

        let inner_pred_for = |d: &mut IntDev<'_>, u: ExprId| -> ExprId {
            let vv_fv = d.fresh_fvar();
            let vv = d.kernel().fvar(vv_fv);
            let au = d.imul(a, u);
            let nv = d.imul(n, vv);
            let sum = d.iadd(au, nv);
            let body = d.ieq(g_i, sum);
            d.lam_fv(vv_fv, int_ty, body)
        };
        let outer_pred = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_pred = inner_pred_for(d, u);
            let exists = d.kernel().const_(exists_name, vec![one_level]);
            let body = d.apply(exists, &[int_ty, inner_pred]);
            d.lam_fv(u_fv, int_ty, body)
        };

        let minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_pred = inner_pred_for(d, u);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let ha_ty = {
                let exists = d.kernel().const_(exists_name, vec![one_level]);
                d.apply(exists, &[int_ty, inner_pred])
            };

            let inner_minor = {
                let vv_fv = d.fresh_fvar();
                let vv = d.kernel().fvar(vv_fv);
                let au = d.imul(a, u);
                let nv = d.imul(n, vv);
                let sum = d.iadd(au, nv);
                let eq_ty = d.ieq(g_i, sum);
                let eq_fv = d.fresh_fvar();
                let eq_h = d.kernel().fvar(eq_fv);

                // one = a*u + n*v
                let one_eq_sum = {
                    let rev = d.isymm(g_i, one_i, cast_eq);
                    d.itrans(one_i, g_i, sum, rev, eq_h)
                };
                // one = n*v + a*u  (commute the sum)
                let comm = d.const_app(p.add_comm, &[au, nv]);
                let nv_au = d.iadd(nv, au);
                let one_eq_comm = d.itrans(one_i, sum, nv_au, one_eq_sum, comm);

                // one - a*u = n*v, via `add_neg_cancel_right (n*v) (a*u)`.
                let neg_au = d.ineg(au);
                let lhs = d.iadd(one_i, neg_au);
                let rhs_start = d.iadd(nv_au, neg_au);
                let step1 = d.icongr(one_i, nv_au, one_eq_comm, &|d, t| d.iadd(t, neg_au));
                let cancel = d.const_app(p.add_neg_cancel_right, &[nv, au]);
                let (_, diff_eq) = d.ichain(lhs, &[(rhs_start, step1), (nv, cancel)]);

                // n ∣ (one - a*u), witness v.
                let dvd_diff = idvd_intro(d, n, lhs, vv, diff_eq);

                // ModEq n (a*u) one, from `modEq_iff_dvd`.
                let modeq_ty = super::modeq::imodeq(d, n, au, one_i);
                let dvd_ty = idvd(d, n, lhs);
                let iff_ty = d.const_app(p.mod_eq_iff_dvd, &[n, au, one_i, h_pos]);
                let mpr = d.const_app(p.logic.iff_mpr, &[modeq_ty, dvd_ty, iff_ty]);
                let modeq_proof = d.apply(mpr, &[dvd_diff]);

                // ∃ b, ModEq n (a*b) one, witness u.
                let intro_name = d.int().logic.exists_intro;
                let intro = d.kernel().const_(intro_name, vec![one_level]);
                let witness_intro = d.apply(intro, &[int_ty, goal_pred, u, modeq_proof]);

                let with_eq = d.lam_fv(eq_fv, eq_ty, witness_intro);
                d.lam_fv(vv_fv, int_ty, with_eq)
            };
            let eliminated = int_exists_elim(d, inner_pred, goal, ha, inner_minor);
            let with_ha = d.lam_fv(ha_fv, ha_ty, eliminated);
            d.lam_fv(u_fv, int_ty, with_ha)
        };

        let disjunction_result = int_exists_elim(d, outer_pred, goal, bez, minor);
        let with_h1 = d.lam_fv(h1_fv, coprime_ty, disjunction_result);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_h1);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.euclid_lemma : ∀ (p a b : Int),
/// (2 ≤ natAbs p ∧ ∀ d, d ∣ natAbs p → d = 1 ∨ d = natAbs p) →
/// p ∣ a*b → p ∣ a ∨ p ∣ b` — Elements VII.30.
///
/// Primality is stated on `natAbs p`, mirroring `Nat.euclid_lemma`'s own
/// inline convention exactly (this prelude has no `Prime` name, over either
/// carrier): a divisor of `natAbs p` is `1` or `natAbs p` itself.
///
/// Transported from the `ℕ` development, not re-derived: let
/// `g = Int.gcd p a` (a `Nat`). `g ∣ natAbs p` (`Nat.gcd_dvd_left`), so
/// primality gives `g = 1` or `g = natAbs p`.
///
/// * `g = natAbs p` — `g ∣ natAbs a` (`Nat.gcd_dvd_right`) transports along
///   the equality to `natAbs p ∣ natAbs a`, and [`declare_dvd_of_nat_abs_dvd`]
///   lifts that to `p ∣ a`.
/// * `g = 1` — this literally **is** `Coprime p a` (`Int.gcd p a = 1`), so
///   [`declare_gauss_lemma`] applied to the hypothesis `p ∣ a*b` closes
///   `p ∣ b` directly — no Euclidean algorithm re-derived, no case split on
///   sign.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_euclid_lemma(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.euclid_lemma, 3, &|d, v| {
        let (pr, a, b) = (v[0], v[1], v[2]);
        let big_pr = nat_abs(d, pr);
        let big_a = nat_abs(d, a);

        let divisor_clause = |d: &mut IntDev<'_>| -> ExprId {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hyp = d.dvd(x, big_pr);
            let one_nat = d.num(1);
            let is_one = d.eq(x, one_nat);
            let is_prime = d.eq(x, big_pr);
            let disjunction = d.or(is_one, is_prime);
            let inner = d.arrow(hyp, disjunction);
            let nat = d.nat_ty();
            d.pi_fv(x_fv, nat, inner)
        };
        let two_nat = d.num(2);
        let two_le = d.le(two_nat, big_pr);
        let clause = divisor_clause(d);
        let prime_ty = d.and(two_le, clause);

        let ab = d.imul(a, b);
        let divides_product = idvd(d, pr, ab);
        let divides_a = idvd(d, pr, a);
        let divides_b = idvd(d, pr, b);
        let conclusion = d.or(divides_a, divides_b);
        let stmt = {
            let inner = d.arrow(divides_product, conclusion);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let product_fv = d.fresh_fvar();
        let product_hyp = d.kernel().fvar(product_fv);

        let clause_proof = d.and_right(two_le, clause, prime_hyp);

        let g = igcd(d, pr, a);
        let common_divides_prime = d.lemma(p.nat.gcd_dvd_left, &[big_pr, big_a]);
        let split = d.apply(clause_proof, &[g, common_divides_prime]);
        let one_nat = d.num(1);
        let is_one_ty = d.eq(g, one_nat);
        let is_prime_ty = d.eq(g, big_pr);

        let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            // h : Eq Nat g 1, i.e. Coprime pr a (Int.gcd pr a is built the
            // same way `Coprime`'s own body does).
            let result = d.const_app(p.gauss_lemma, &[pr, a, b, h, product_hyp]);
            d.or_inr(divides_a, divides_b, result)
        };
        let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            // h : Eq Nat g big_pr.
            let base = d.lemma(p.nat.gcd_dvd_right, &[big_pr, big_a]);
            let motive = |d: &mut IntDev<'_>, x: ExprId| d.dvd(x, big_a);
            let rewritten = d.nat_rewrite(g, big_pr, h, base, &motive);
            let lifted = d.const_app(p.dvd_of_nat_abs_dvd, &[pr, a, rewritten]);
            d.or_inl(divides_a, divides_b, lifted)
        };
        let disjunction_result =
            d.or_elim(is_one_ty, is_prime_ty, conclusion, split, on_left, on_right);

        let with_product = d.lam_fv(product_fv, divides_product, disjunction_result);
        let proof = d.lam_fv(prime_fv, prime_ty, with_product);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.euclid_infinitude` — Euclid's theorem, transported from `ℕ`.
// ---------------------------------------------------------------------------

/// `2 ≤ magnitude ∧ ∀ (x : Nat), x ∣ magnitude → Eq Nat x 1 ∨ Eq Nat x magnitude`.
///
/// The same inline primality convention `euclid_lemma` uses (Elements VII,
/// Def. 11), spelled out again here rather than shared: five lines, and this
/// prelude has no `Prime` name over either carrier (see the decision note on
/// [`declare_euclid_infinitude`]).
fn int_prime_condition(d: &mut IntDev<'_>, magnitude: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let two_le = d.le(two_nat, magnitude);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hyp = d.dvd(x, magnitude);
    let is_one = d.eq(x, one_nat);
    let is_whole = d.eq(x, magnitude);
    let disjunction = d.or(is_one, is_whole);
    let inner = d.arrow(hyp, disjunction);
    let clause = d.pi_fv(x_fv, nat, inner);
    d.and(two_le, clause)
}

/// `fun (p : Int) => And (lt n p) (int_prime_condition (natAbs p))`.
fn euclid_pred(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let p_fv = d.fresh_fvar();
    let p_var = d.kernel().fvar(p_fv);
    let strict = d.ilt(n, p_var);
    let big_p = nat_abs(d, p_var);
    let prime = int_prime_condition(d, big_p);
    let body = d.and(strict, prime);
    d.lam_fv(p_fv, int_ty, body)
}

/// `∃ (p : Int), n < p ∧ (2 ≤ natAbs p ∧ ∀ x, x ∣ natAbs p → x=1 ∨ x=natAbs p)`,
/// for the `n` in `v[0]`.
fn euclid_infinitude_stmt(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let n = v[0];
    let int_ty = d.int_ty();
    let one = d.level_one();
    let pred = euclid_pred(d, n);
    let exists_name = d.int().logic.exists_;
    let exists_c = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists_c, &[int_ty, pred])
}

/// `Int.euclid_infinitude : ∀ (n : Int), ∃ (p : Int), n < p ∧
/// (2 ≤ natAbs p ∧ ∀ (x : Nat), x ∣ natAbs p → x = 1 ∨ x = natAbs p)`.
///
/// Transported from `Nat.exists_prime_gt` (Euclid's theorem, already proved,
/// not re-derived here): given `n`, case-split on its sign and let `m` be its
/// magnitude (`natAbs n`, computed directly from the branch's own `Nat`
/// field — `m'` for `ofNat m'`, `succ k` for `negSucc k`). `Nat.exists_prime_gt
/// m` gives a `Nat` prime `q` with `m < q`; the witness is `p := ofNat q` for
/// **both** branches.
///
/// * `n = ofNat m'`: `Int.lt (ofNat m') (ofNat q)` reduces to `Nat.lt m' q`,
///   exactly `Nat.exists_prime_gt`'s own bound (`m` was built as `m'`, no
///   conversion needed).
/// * `n = negSucc k`: `Int.lt (negSucc k) (ofNat q)` reduces to `True`
///   outright — every non-negative integer exceeds every negative one,
///   independent of `q` — so the bound half of `Nat.exists_prime_gt`'s
///   witness is discarded and only its primality half is used.
///
/// Either way, primality of `natAbs (ofNat q) ≡ q` is `Nat.exists_prime_gt`'s
/// own conclusion with no extra work, because [`int_prime_condition`] is
/// built to the identical shape as `Nat`'s own (unnamed) primality clause.
///
/// ## Why no `Int.Prime`/`Nat.Prime`
///
/// This development introduces a `Prime` name on **neither** carrier.
/// `Nat.euclid_lemma`/`Nat.exists_prime_gt` already state primality inline
/// (`2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`), and `Int.euclid_lemma` mirrors that
/// convention rather than introducing a name unilaterally on `ℤ`. Adding
/// `Int.Prime` alone would make the two carriers state the *same* mathematical
/// idea two different ways for no reason but convenience at the call site;
/// adding `Nat.Prime` too is out of scope here (`nat_prelude/` is another
/// lane's file today). Consistency across carriers — one convention, applied
/// everywhere — outweighs the naming convenience, so neither carrier gets the
/// name until both can get it together.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_euclid_infinitude(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.euclid_infinitude, 1, &|d, v| {
        let stmt = euclid_infinitude_stmt(d, v);
        let proof = case_split(d, v, &euclid_infinitude_stmt, &|d, b| {
            let field = b[0].1;
            let m = match b[0].0 {
                Shape::OfNat => field,
                Shape::NegSucc => d.succ(field),
            };
            let n_branch = d.branch_term(b[0]);

            let source = d.const_app(p.nat.exists_prime_gt, &[m]);
            let source_pred = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let bound = d.lt(m, q);
                let prime = int_prime_condition(d, q);
                let body = d.and(bound, prime);
                let nat = d.nat_ty();
                d.lam_fv(q_fv, nat, body)
            };

            let target = euclid_infinitude_stmt(d, &[n_branch]);
            let pred_branch = euclid_pred(d, n_branch);

            let minor = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let bound_ty = d.lt(m, q);
                let prime_ty = int_prime_condition(d, q);
                let h_ty = d.and(bound_ty, prime_ty);

                let h_lt = d.and_left(bound_ty, prime_ty, h);
                let h_prime = d.and_right(bound_ty, prime_ty, h);

                let witness = d.of_nat(q);
                let strict_proof = match b[0].0 {
                    Shape::OfNat => h_lt,
                    Shape::NegSucc => d.true_intro(),
                };
                let big_witness = nat_abs(d, witness);
                let strict_ty = d.ilt(n_branch, witness);
                let prime_ty2 = int_prime_condition(d, big_witness);
                let and_proof = {
                    let name = d.int().logic.and_intro;
                    d.const_app(name, &[strict_ty, prime_ty2, strict_proof, h_prime])
                };

                let one_level = d.level_one();
                let int_ty = d.int_ty();
                let intro_name = d.int().logic.exists_intro;
                let intro = d.kernel().const_(intro_name, vec![one_level]);
                let exists_proof = d.apply(intro, &[int_ty, pred_branch, witness, and_proof]);

                let nat = d.nat_ty();
                let with_h = d.lam_fv(h_fv, h_ty, exists_proof);
                d.lam_fv(q_fv, nat, with_h)
            };
            exists_elim(d, source_pred, target, source, minor)
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Nat.exists_mul_mod_eq_gcd`.
// ---------------------------------------------------------------------------

/// `exists_mul_mod_eq_gcd : ∀ n k, Nat.gcd n k < k →
/// ∃ m, m < k ∧ n*m % k = Nat.gcd n k` — Mathlib v4.30's
/// `Nat.exists_mul_mod_eq_gcd`.
///
/// The Bézout coefficient `Nat.gcdA n k` (an `Int`, possibly negative)
/// already satisfies `ofNat (gcd n k) = ofNat n * gcdA n k + ofNat k *
/// gcdB n k` (`bezout_witnesses::declare_nat_gcd_eq_gcd_ab`). Reducing that
/// coefficient modulo `k` throws away the `ofNat k * gcdB n k` summand — an
/// exact multiple of the modulus, via `Int.modEq_add_mul_left` — and lands a
/// genuine `Nat` witness `m := natAbs (gcdA n k % k)` in `[0, k)`. Every step
/// past the Bézout identity is modular-arithmetic bookkeeping already proved
/// in `modeq.rs`/`modeq_family.rs` (`Int.ModEq.mul_left`, `Int.mod_modEq`,
/// `Int.ModEq.symm`), plus one use of
/// [`super::wilson::emod_eq_self_of_in_range`] to identify
/// `emod (ofNat (gcd n k)) (ofNat k)` with `ofNat (gcd n k)` itself under the
/// hypothesis. The final `Int` equation `ofNat (gcd n k) = ofNat (n*m % k)`
/// descends to the stated `Nat` equation by `natAbs`, which is the identity
/// on `ofNat` by computation.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_exists_mul_mod_eq_gcd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.exists_mul_mod_eq_gcd, 2, &|d, v| {
        let (n_var, k_var) = (v[0], v[1]);
        let g_nat = NatOps::gcd(d, n_var, k_var);
        let hyp_ty = d.lt(g_nat, k_var);

        let nat = d.nat_ty();
        let pred = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let bound = d.lt(m, k_var);
            let nm = NatOps::mul(d, n_var, m);
            let modv = d.modulo(nm, k_var);
            let eqn = d.eq(modv, g_nat);
            let body = d.and(bound, eqn);
            d.lam_fv(m_fv, nat, body)
        };
        let one = d.level_one();
        let exists_ty = {
            let exists_name = d.int().logic.exists_;
            let e = d.kernel().const_(exists_name, vec![one]);
            d.apply(e, &[nat, pred])
        };
        let stmt = d.arrow(hyp_ty, exists_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // --- 0 < k, both as Nat and (by defeq, since `Int.lt`/`Int.zero`
        // ι-reduce to `Nat.lt`/`ofNat Nat.zero` on `ofNat`-shaped arguments)
        // as `Int.lt Int.zero (ofNat k)` -------------------------------------
        let zero_nat = d.zero();
        let zero_le_g = d.lemma(p.nat.zero_le, &[g_nat]);
        let k_pos_nat = d.lemma(
            p.nat.lt_of_le_of_lt,
            &[zero_nat, g_nat, k_var, zero_le_g, h],
        );

        let big_k = d.of_nat(k_var);
        let big_g = d.of_nat(g_nat);

        // --- emod (ofNat g) (ofNat k) = ofNat g, from `0 <= g < k` ----------
        let emod_g_eq_g =
            super::wilson::emod_eq_self_of_in_range(d, big_g, big_k, k_pos_nat, zero_le_g, h);

        // --- Bezout: ofNat g = ofNat n * u + ofNat k * v --------------------
        let u = d.const_app(p.nat_gcd_a, &[n_var, k_var]);
        let vv = d.const_app(p.nat_gcd_b, &[n_var, k_var]);
        let big_n = d.of_nat(n_var);
        let nu = d.imul(big_n, u);
        let kv = d.imul(big_k, vv);
        let eq1 = d.lemma(p.nat_gcd_eq_gcd_ab, &[n_var, k_var]); // ofNat g = nu + kv

        let commuted = d.const_app(p.add_comm, &[nu, kv]); // nu+kv = kv+nu
        let nu_plus_kv = d.iadd(nu, kv);
        let kv_plus_nu = d.iadd(kv, nu);
        let g_eq_kvnu = d.itrans(big_g, nu_plus_kv, kv_plus_nu, eq1, commuted);

        // --- ModEq k (kv+nu) nu, transported to ModEq k g nu ----------------
        let shift = d.const_app(p.mod_eq_add_mul_left, &[big_k, nu, vv]); // ModEq k (k*v+nu) nu
        let kvnu_eq_g = d.isymm(big_g, kv_plus_nu, g_eq_kvnu);
        let g_modeq_nu = d.int_eq_rewrite(kv_plus_nu, big_g, kvnu_eq_g, shift, &|d, t| {
            super::modeq::imodeq(d, big_k, t, nu)
        });

        // --- g = emod(g,k) = emod(nu,k) --------------------------------------
        let emod_g_k = d.iemod(big_g, big_k);
        let emod_nu_k = d.iemod(nu, big_k);
        let g_eq_emod_g = d.isymm(emod_g_k, big_g, emod_g_eq_g);
        let g_eq_emod_nu = d.itrans(big_g, emod_g_k, emod_nu_k, g_eq_emod_g, g_modeq_nu);

        // --- reduce u modulo k to a bounded Nat witness ---------------------
        let ne_k = super::dvd::ne_zero_of_pos(d, big_k, k_pos_nat);
        let r = d.iemod(u, big_k);
        let r_nonneg = d.const_app(p.emod_nonneg, &[u, big_k, ne_k]);
        let r_lt = d.const_app(p.emod_lt_of_pos, &[u, big_k, k_pos_nat]);

        let m_nat = nat_abs(d, r);
        let r_eq_ofm = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r, r_nonneg]); // ofNat m = r
        let big_m = d.of_nat(m_nat);
        let r_eq_ofm_rev = d.isymm(big_m, r, r_eq_ofm); // r = ofNat m

        let m_lt_k = d.int_eq_rewrite(r, big_m, r_eq_ofm_rev, r_lt, &|d, t| d.ilt(t, big_k));

        // --- u = m (mod k), hence n*u = n*m (mod k) --------------------------
        let r_modeq_u = d.const_app(p.mod_mod_eq, &[u, big_k]); // ModEq k r u
        let u_modeq_r = d.const_app(p.mod_eq_symm, &[big_k, r, u, r_modeq_u]); // ModEq k u r
        let mul_left_step = d.const_app(p.mod_eq_mul_left, &[big_k, u, r, big_n]);
        let nu_modeq_nr = d.apply(mul_left_step, &[k_pos_nat, u_modeq_r]); // ModEq k nu (n*r)

        let nr = d.imul(big_n, r);
        let emod_nr_k = d.iemod(nr, big_k);
        let g_eq_emod_nr = d.itrans(big_g, emod_nu_k, emod_nr_k, g_eq_emod_nu, nu_modeq_nr);

        // --- replace r by ofNat m, exposing n*m % k by computation ----------
        let g_eq_emod_nm = d.int_eq_rewrite(r, big_m, r_eq_ofm_rev, g_eq_emod_nr, &|d, t| {
            let nt = d.imul(big_n, t);
            let em = d.iemod(nt, big_k);
            d.ieq(big_g, em)
        });

        // `emod (ofNat n * ofNat m) (ofNat k)` reduces (ι) to
        // `ofNat (Nat.mod (Nat.mul n m) k)`, so `g_eq_emod_nm` is *also* a
        // term of type `Eq Int (ofNat g) (ofNat (n*m % k))` by defeq.
        let modk_expr = {
            let nm = NatOps::mul(d, n_var, m_nat);
            d.modulo(nm, k_var)
        };
        let of_modk = d.of_nat(modk_expr);
        let raw_nat_eq = icongr_nat(d, big_g, of_modk, g_eq_emod_nm, &|d, x| nat_abs(d, x));
        let final_eq = d.symm(g_nat, modk_expr, raw_nat_eq); // Eq Nat (n*m%k) g

        let bound_ty = d.lt(m_nat, k_var);
        let eq_ty = d.eq(modk_expr, g_nat);
        let and_proof = {
            let name = d.int().logic.and_intro;
            d.const_app(name, &[bound_ty, eq_ty, m_lt_k, final_eq])
        };

        let intro_name = d.int().logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one]);
        let exists_proof = d.apply(intro, &[nat, pred, m_nat, and_proof]);

        let proof = d.lam_fv(h_fv, hyp_ty, exists_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.gcd_div_gcd_div_gcd : ∀ i j, Nat.lt zero (gcd i j) →
/// Eq Nat (gcd (i.ediv (ofNat (gcd i j))) (j.ediv (ofNat (gcd i j)))) one` —
/// Mathlib v4.30's `Int.gcd_div_gcd_div_gcd`: dividing both operands by their
/// own gcd leaves a coprime pair.
///
/// An INDEPENDENT Bézout route, not a corollary of `Int.gcd_div` (this
/// development has no exact-quotient-uniqueness argument for a general,
/// possibly negative, divisor — see `docs/plan/status/234-int-gcd-div.md`).
/// The divisor here, `ofNat (gcd i j)`, is always nonnegative (a `Nat` cast),
/// so that gap never comes up.
///
/// Sketch, with `g := gcd i j`, `c := ofNat g`, `qi := i.ediv c`,
/// `qj := j.ediv c`, `u := gcdA i j`, `v := gcdB i j`,
/// `X := (qi*u) + (qj*v)`:
///
/// - `c` divides `i` and `j` exactly ([`declare_gcd_dvd_left_right`] +
///   `emod_eq_zero_iff_dvd` + `ediv_add_emod`), so `i = c*qi`, `j = c*qj`.
/// - Bézout ([`bezout_witnesses::declare_gcd_eq_gcd_ab_witnesses`]) gives
///   `c = i*u + j*v`; substituting and factoring (`mul_assoc`/
///   `left_distrib`) turns that into `c = c*X`, hence `c*1 = c*X`.
/// - Taking `natAbs` of both sides (`nat_abs_mul`) and cancelling the shared
///   positive factor `g` (`Nat.mul_left_cancel_of_pos`, fed `h` itself for
///   the `Le one g` premise — `Nat.lt` unfolds to exactly that shape) gives
///   `natAbs X = 1`.
/// - `gcd qi qj` divides `qi*u` and `qj*v` ([`declare_gcd_dvd_left_right`] +
///   `dvd_mul_right` + `dvd_trans`), hence divides their sum `X`
///   (`dvd_add`), hence divides `natAbs X = 1`
///   ([`declare_nat_abs_dvd_nat_abs_of_dvd`]), hence equals `1`
///   (`Nat.eq_one_of_dvd_one`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gcd_div_gcd_div_gcd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_div_gcd_div_gcd, 2, &|d, v| {
        let (i, j) = (v[0], v[1]);
        let g = igcd(d, i, j);
        let zero_nat = d.zero();
        let hyp_ty = d.lt(zero_nat, g);

        let c = d.of_nat(g);
        let qi = d.iediv(i, c);
        let qj = d.iediv(j, c);
        let g2 = igcd(d, qi, qj);
        let one_nat = d.num(1);
        let concl = d.eq(g2, one_nat);
        let stmt = d.arrow(hyp_ty, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let zero_i = d.izero();

        // --- `a = c*(a/c)`, given `c` divides `a` exactly. -------------------
        let exact = |d: &mut IntDev<'_>, a: ExprId, dvd_c_a: ExprId| -> ExprId {
            let ediv_ac = d.iediv(a, c);
            let emod_ac = d.iemod(a, c);
            let zero_eq_ty = d.ieq(emod_ac, zero_i);
            let dvd_ty = idvd(d, c, a);
            let iff_ac = d.const_app(p.emod_eq_zero_iff_dvd, &[a, c, h]);
            let mpr = d.const_app(p.logic.iff_mpr, &[zero_eq_ty, dvd_ty, iff_ac]);
            let emod_eq_zero = d.apply(mpr, &[dvd_c_a]);

            let mul_q = d.imul(c, ediv_ac);
            let sum_with_emod = d.iadd(mul_q, emod_ac);
            let full_eq = d.const_app(p.ediv_add_emod, &[a, c]); // Eq(sum_with_emod, a)
            let full_eq_rev = d.isymm(sum_with_emod, a, full_eq); // Eq(a, sum_with_emod)
            let sum_with_zero = d.iadd(mul_q, zero_i);
            let step = d.icongr(emod_ac, zero_i, emod_eq_zero, &|d, x| d.iadd(mul_q, x));
            let add_zero_q = d.const_app(p.add_zero, &[mul_q]); // Eq(sum_with_zero, mul_q)
            let (_, chained) =
                d.ichain(sum_with_emod, &[(sum_with_zero, step), (mul_q, add_zero_q)]);
            d.itrans(a, sum_with_emod, mul_q, full_eq_rev, chained) // Eq(a, c*(a/c))
        };

        let dvd_c_i = d.const_app(p.gcd_dvd_left, &[i, j]); // idvd(c, i)
        let dvd_c_j = d.const_app(p.gcd_dvd_right, &[i, j]); // idvd(c, j)
        let i_eq_cqi = exact(d, i, dvd_c_i); // Eq Int i (c*qi)
        let j_eq_cqj = exact(d, j, dvd_c_j); // Eq Int j (c*qj)

        // --- Bézout: `c = i*u + j*v`. ------------------------------------------
        let u = d.const_app(p.gcd_a, &[i, j]);
        let vv = d.const_app(p.gcd_b, &[i, j]);
        let eq_bezout = d.lemma(p.gcd_eq_gcd_ab_witnesses, &[i, j]); // Eq(c, i*u+j*v)

        let iu = d.imul(i, u);
        let jv = d.imul(j, vv);

        let icqi = d.imul(c, qi);
        let jcqj = d.imul(c, qj);
        let icqiu = d.imul(icqi, u);
        let jcqjv = d.imul(jcqj, vv);

        let iu_to_icqiu = d.icongr(i, icqi, i_eq_cqi, &|d, x| d.imul(x, u));
        let jv_to_jcqjv = d.icongr(j, jcqj, j_eq_cqj, &|d, x| d.imul(x, vv));

        let step_sum1 = d.icongr(iu, icqiu, iu_to_icqiu, &|d, x| d.iadd(x, jv));
        let step_sum2 = d.icongr(jv, jcqjv, jv_to_jcqjv, &|d, x| d.iadd(icqiu, x));

        let iu_plus_jv = d.iadd(iu, jv);
        let icqiu_plus_jv = d.iadd(icqiu, jv);
        let icqiu_plus_jcqjv = d.iadd(icqiu, jcqjv);
        let (_, sub_chained) = d.ichain(
            iu_plus_jv,
            &[(icqiu_plus_jv, step_sum1), (icqiu_plus_jcqjv, step_sum2)],
        );

        let c_eq_prod = d.itrans(c, iu_plus_jv, icqiu_plus_jcqjv, eq_bezout, sub_chained);

        // --- Factor `c` out: `(c*qi)*u + (c*qj)*v = c*(qi*u) + c*(qj*v) = c*X`.
        let qi_u = d.imul(qi, u);
        let qj_v = d.imul(qj, vv);
        let c_qiu = d.imul(c, qi_u);
        let c_qjv = d.imul(c, qj_v);

        let assoc_i = d.const_app(p.mul_assoc, &[c, qi, u]); // Eq(icqiu, c_qiu)
        let assoc_j = d.const_app(p.mul_assoc, &[c, qj, vv]); // Eq(jcqjv, c_qjv)

        let step3 = d.icongr(icqiu, c_qiu, assoc_i, &|d, x| d.iadd(x, jcqjv));
        let step4 = d.icongr(jcqjv, c_qjv, assoc_j, &|d, x| d.iadd(c_qiu, x));

        let c_qiu_plus_jcqjv = d.iadd(c_qiu, jcqjv);
        let c_qiu_plus_c_qjv = d.iadd(c_qiu, c_qjv);
        let (_, factor_chained) = d.ichain(
            icqiu_plus_jcqjv,
            &[(c_qiu_plus_jcqjv, step3), (c_qiu_plus_c_qjv, step4)],
        );

        let x_expr = d.iadd(qi_u, qj_v);
        let c_x = d.imul(c, x_expr);
        let distrib = d.const_app(p.left_distrib, &[c, qi_u, qj_v]); // Eq(c_x, c_qiu_plus_c_qjv)
        let distrib_rev = d.isymm(c_x, c_qiu_plus_c_qjv, distrib);

        let (_, c_eq_cx) = d.ichain(
            c,
            &[
                (icqiu_plus_jcqjv, c_eq_prod),
                (c_qiu_plus_c_qjv, factor_chained),
                (c_x, distrib_rev),
            ],
        );

        // --- `c*1 = c*X`. -------------------------------------------------------
        let one_i = d.ione();
        let c_one = d.imul(c, one_i);
        let mul_one_c = d.const_app(p.mul_one, &[c]); // Eq(c_one, c)
        let c1_eq_cx = d.itrans(c_one, c, c_x, mul_one_c, c_eq_cx);

        // --- `natAbs` both sides, expand the products, cancel `g`. -------------
        let nat_abs_c = nat_abs(d, c);
        let nat_abs_1 = nat_abs(d, one_i);
        let nat_abs_x = nat_abs(d, x_expr);
        let nat_abs_c_one = nat_abs(d, c_one);
        let nat_abs_c_x = nat_abs(d, c_x);

        let nat_abs_congr_step = icongr_nat(d, c_one, c_x, c1_eq_cx, &|d, y| nat_abs(d, y));
        // Eq Nat nat_abs_c_one nat_abs_c_x

        let lhs_mul = NatOps::mul(d, nat_abs_c, nat_abs_1);
        let rhs_mul = NatOps::mul(d, nat_abs_c, nat_abs_x);
        let mul_c1 = d.const_app(p.nat_abs_mul, &[c, one_i]); // Eq(nat_abs_c_one, lhs_mul)
        let mul_cx = d.const_app(p.nat_abs_mul, &[c, x_expr]); // Eq(nat_abs_c_x, rhs_mul)
        let mul_c1_rev = d.symm(nat_abs_c_one, lhs_mul, mul_c1); // Eq(lhs_mul, nat_abs_c_one)

        let (_, eq5) = d.chain(
            lhs_mul,
            &[
                (nat_abs_c_one, mul_c1_rev),
                (nat_abs_c_x, nat_abs_congr_step),
                (rhs_mul, mul_cx),
            ],
        ); // eq5 : Eq Nat lhs_mul rhs_mul

        // `h : Nat.lt zero g` unfolds to exactly `Nat.le one nat_abs_c`
        // (`nat_abs_c` ι-reduces to `g`, `Nat.lt` δ-unfolds to `Nat.le (succ ·) ·`).
        let cancelled = d.lemma(
            p.nat.mul_left_cancel_of_pos,
            &[nat_abs_c, nat_abs_1, nat_abs_x, h, eq5],
        ); // Eq Nat nat_abs_1 nat_abs_x

        // --- `gcd qi qj` divides `natAbs X`, hence equals `1`. ------------------
        let of_g2 = d.of_nat(g2);
        let dvd_qi = d.const_app(p.gcd_dvd_left, &[qi, qj]); // idvd(of_g2, qi)
        let dvd_qj = d.const_app(p.gcd_dvd_right, &[qi, qj]); // idvd(of_g2, qj)

        let dvd_qi_u = {
            let step = d.const_app(p.dvd_mul_right, &[qi, u]); // idvd(qi, qi*u)
            d.const_app(p.dvd_trans, &[of_g2, qi, qi_u, dvd_qi, step])
        };
        let dvd_qj_v = {
            let step = d.const_app(p.dvd_mul_right, &[qj, vv]); // idvd(qj, qj*v)
            d.const_app(p.dvd_trans, &[of_g2, qj, qj_v, dvd_qj, step])
        };
        let dvd_x = d.const_app(p.dvd_add, &[of_g2, qi_u, qj_v, dvd_qi_u, dvd_qj_v]);
        // idvd(of_g2, x_expr)

        let nat_dvd_x = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_g2, x_expr, dvd_x]);
        // Nat.dvd (natAbs of_g2) nat_abs_x, i.e. Nat.dvd g2 nat_abs_x up to defeq.

        let cancelled_rev = d.symm(nat_abs_1, nat_abs_x, cancelled); // Eq nat_abs_x nat_abs_1
        let nat_dvd_1 = d.nat_rewrite(nat_abs_x, nat_abs_1, cancelled_rev, nat_dvd_x, &|d, w| {
            d.dvd(g2, w)
        });

        let proof_body = d.lemma(p.nat.eq_one_of_dvd_one, &[g2, nat_dvd_1]); // Eq Nat g2 one_nat
        let proof = d.lam_fv(h_fv, hyp_ty, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.gcd_div` — dividing two integers by a COMMON divisor of arbitrary sign
// (or zero) divides their gcd by its magnitude.
// ---------------------------------------------------------------------------
//
// Mathlib v4.30's `Int.gcd_div` is `alias gcd_div := gcd_ediv`, and Lean 4
// core's `Int.gcd_ediv` (`Init.Data.Int.Gcd`) states it over `/`, which core's
// own `instance : Div Int` binds to `Int.ediv` "for compatibility with
// SMT-LIB" (`Init.Data.Int.DivMod.Basic`) — the SAME division this
// development's `Int.ediv` already matches bit for bit. So this is a
// same-definition mirror, not a restatement of a different proposition, and
// it carries NO restriction on `c`'s sign (Mathlib's own hypotheses are only
// `c ∣ a`, `c ∣ b`) -- `c = 0` is a genuine, if degenerate, case of the
// statement and is proved here rather than excluded.
//
// The proof does NOT go through `Nat.gcd_mul_left`/`gcd_mul_right` (Lean
// core's own route, via `Nat.gcd_div`): neither exists in this development,
// and building either would need a fresh strong-induction principle over
// `Nat.gcd`'s well-founded recursion (see the `WellFounded.fix`-based
// `gcd_dvd`/`dvd_gcd`/`gcd_bezout` constructions earlier in this file for
// what that costs). Instead this is MUTUAL DIVISIBILITY, generalizing
// [`declare_gcd_div_gcd_div_gcd`]'s Bézout route rather than
// `Nat.gcd_div`'s cancellation route:
//
// With `qa := a.ediv c`, `qb := b.ediv c`, `C := natAbs c`, `G := gcd a b`,
// `H := gcd qa qb`, and (for `c ≠ 0`) `K := G / C` (exact, since `C ∣ G`
// follows directly from `c ∣ a`, `c ∣ b` via `nat_abs_dvd_nat_abs_of_dvd` +
// `Nat.dvd_gcd` -- no Bézout needed for THIS half):
//
// - **`H ∣ K`.** Bézout on `a, b` gives `ofNat G = a*u + b*v`; substituting
//   `a = c*qa`, `b = c*qb` and factoring gives `ofNat G = c*X` for
//   `X := qa*u + qb*v` -- an UNCONDITIONAL equation, no sign case needed.
//   Taking `natAbs` of both sides: `G = C * natAbs X`. Combined with
//   `C*K = G` and cancelling the shared positive factor `C`
//   (`Nat.mul_left_cancel_of_pos`): `natAbs X = K`. Separately, `H` divides
//   `qa` and `qb` (`gcd_dvd_left`/`_right`), hence `qa*u` and `qb*v`
//   (`dvd_mul_right`), hence their sum `X` (`dvd_add`); taking `natAbs`
//   (`nat_abs_dvd_nat_abs_of_dvd`) gives `H ∣ natAbs X = K`.
// - **`K ∣ H`.** Bézout on `qa, qb` gives `ofNat H = qa*u' + qb*v'`;
//   multiplying by `c` and substituting back gives `c*(ofNat H) = a*u' +
//   b*v'`. `G` divides `a` and `b`, hence this sum, hence `c*(ofNat H)`;
//   taking `natAbs`: `G ∣ C*H`. Since `G = C*K`, this is `C*K ∣ C*H`;
//   cancelling `C` from the divisibility itself (not just an equation --
//   [`cancel_dvd_of_pos`], built locally since no such lemma exists yet)
//   gives `K ∣ H`.
// - `Nat.dvd_antisymm` closes `H = K = G/C`.
//
// Neither direction needed `c`'s sign decomposed into `±ofNat C` at any
// point -- only `natAbs` identities, which hold unconditionally. The sign
// case split that DOES remain (`c = 0`, `c = ofNat (succ m)`, `c = negSucc
// n`) exists only to supply `c ≠ 0` (for [`super::dvd::ne_zero_of_pos`]/
// discrimination) and `1 ≤ natAbs c` (for the two cancellations), and to
// handle `c = 0` separately, where both sides collapse to `0` via
// `gcd_zero_right`/`Nat.zero_div`.

/// From `h_dvd : Nat.dvd (cabs*x) (cabs*y)` and `1 ≤ cabs`, derive
/// `Nat.dvd x y` -- cancel a shared positive factor out of a divisibility
/// statement itself, not just an equation. No such lemma exists in this
/// development; the witness manipulation is short enough to build locally
/// (eliminate `h_dvd`'s witness `w`, reassociate `(cabs*x)*w` to
/// `cabs*(x*w)` via `Nat.mul_assoc`, cancel `cabs` from the resulting
/// equation via `Nat.mul_left_cancel_of_pos`, and re-introduce `w` as the
/// witness for `Nat.dvd x y`).
fn cancel_dvd_of_pos(
    d: &mut IntDev<'_>,
    cabs: ExprId,
    x: ExprId,
    y: ExprId,
    one_le_cabs: ExprId,
    h_dvd: ExprId,
) -> ExprId {
    let p = d.int();
    let cabs_x = NatOps::mul(d, cabs, x);
    let cabs_y = NatOps::mul(d, cabs, y);
    let pred = d.dvd_predicate(cabs_x, cabs_y);
    let goal = d.dvd(x, y);
    let nat = d.nat_ty();

    let minor = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let cabs_x_w = NatOps::mul(d, cabs_x, w);
        let heq_ty = d.eq(cabs_y, cabs_x_w);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let xw = NatOps::mul(d, x, w);
        let cabs_xw = NatOps::mul(d, cabs, xw);
        let assoc = {
            let name = p.nat.mul_assoc;
            d.const_app(name, &[cabs, x, w])
        }; // Eq Nat (cabs_x*w) cabs_xw
        let (_, chained) = d.chain(cabs_y, &[(cabs_x_w, heq), (cabs_xw, assoc)]);
        // chained : Eq Nat cabs_y cabs_xw

        let y_eq_xw = {
            let name = p.nat.mul_left_cancel_of_pos;
            d.const_app(name, &[cabs, y, xw, one_le_cabs, chained])
        }; // Eq Nat y xw
        let witness_proof = nat_dvd_intro(d, x, y, w, y_eq_xw);
        let with_heq = d.lam_fv(heq_fv, heq_ty, witness_proof);
        d.lam_fv(w_fv, nat, with_heq)
    };
    exists_elim(d, pred, goal, h_dvd, minor)
}

/// `Eq Int x zero` from `h_dvd : Int.dvd zero_int x` (the `Int`-level
/// `dvd zero_int x := ∃ c, x = zero_int*c`). `zero_int*c = c*zero_int`
/// (comm) `= zero_int` (`mul_zero`), so any witness forces `x = zero_int`.
fn zero_dvd_elim(d: &mut IntDev<'_>, x: ExprId, h_dvd: ExprId) -> ExprId {
    let p = d.int();
    let zero_int = d.izero();
    let pred = idvd_predicate(d, zero_int, x);
    let goal = d.ieq(x, zero_int);
    let int_ty = d.int_ty();

    let minor = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let zc = d.imul(zero_int, c);
        let heq_ty = d.ieq(x, zc);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let cz = d.imul(c, zero_int);
        let comm = d.const_app(p.mul_comm, &[zero_int, c]); // Eq Int zc cz
        let mz = d.const_app(p.mul_zero, &[c]); // Eq Int cz zero_int
        let (_, chained) = d.ichain(zc, &[(cz, comm), (zero_int, mz)]);
        let result = d.itrans(x, zc, zero_int, heq, chained);
        let with_heq = d.lam_fv(heq_fv, heq_ty, result);
        d.lam_fv(c_fv, int_ty, with_heq)
    };
    int_exists_elim(d, pred, goal, h_dvd, minor)
}

/// The `Eq Nat` conclusion `gcd (a.ediv c) (b.ediv c) = gcd a b / natAbs c`,
/// at caller-supplied `a, b, cc`.
fn gcd_div_concl(d: &mut IntDev<'_>, a: ExprId, b: ExprId, cc: ExprId) -> ExprId {
    let qa = d.iediv(a, cc);
    let qb = d.iediv(b, cc);
    let lhs = igcd(d, qa, qb);
    let g = igcd(d, a, b);
    let cabs = nat_abs(d, cc);
    let rhs = NatOps::div(d, g, cabs);
    d.eq(lhs, rhs)
}

/// `Int.gcd_div`'s full per-`c`-shape goal: `c ∣ a → c ∣ b → <concl>`.
fn gcd_div_goal(d: &mut IntDev<'_>, a: ExprId, b: ExprId, cc: ExprId) -> ExprId {
    let dvd_ca = idvd(d, cc, a);
    let dvd_cb = idvd(d, cc, b);
    let concl = gcd_div_concl(d, a, b, cc);
    let inner = d.arrow(dvd_cb, concl);
    d.arrow(dvd_ca, inner)
}

/// The degenerate `c = 0` case: `dvd 0 a → dvd 0 b → <concl at c = 0>`.
/// Both `a` and `b` collapse to `zero` (via [`zero_dvd_elim`]), at which
/// point both sides of the conclusion collapse to `0`
/// (`gcd_zero_right`/`Nat.zero_div`), and the general `a, b` case is
/// recovered by two `int_eq_rewrite`s.
fn gcd_div_zero_case(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let zero_int = d.izero();
    let dvd_ca = idvd(d, zero_int, a);
    let dvd_cb = idvd(d, zero_int, b);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let a_eq_zero = zero_dvd_elim(d, a, h1);
    let b_eq_zero = zero_dvd_elim(d, b, h2);
    let zero_eq_a = d.isymm(a, zero_int, a_eq_zero);
    let zero_eq_b = d.isymm(b, zero_int, b_eq_zero);

    let proof0 = gcd_div_concl_zero_zero_zero(d);
    let lifted_a = d.int_eq_rewrite(zero_int, a, zero_eq_a, proof0, &|d, x| {
        gcd_div_concl(d, x, zero_int, zero_int)
    });
    let lifted_ab = d.int_eq_rewrite(zero_int, b, zero_eq_b, lifted_a, &|d, x| {
        gcd_div_concl(d, a, x, zero_int)
    });

    let with_h2 = d.lam_fv(h2_fv, dvd_cb, lifted_ab);
    d.lam_fv(h1_fv, dvd_ca, with_h2)
}

/// A concrete proof of `gcd_div_concl(zero, zero, zero)`: both
/// `ediv (ofNat 0) (ofNat 0)` and `natAbs (ofNat 0)` reduce (pure `Int.rec`
/// `iota`) to `Nat.div zero zero` / `zero` respectively, and
/// `Nat.zero_div`/`gcd_zero_right` close the rest.
fn gcd_div_concl_zero_zero_zero(d: &mut IntDev<'_>) -> ExprId {
    let p = d.int();
    let zero_int = d.izero();
    let nat_zero = d.zero();

    // qa0 := ediv(zero,zero) = zero_int, via `Nat.zero_div` bridged across
    // the `ediv`/`Int.rec` `iota` reduction by a plain `d.irefl`.
    let qa0 = d.iediv(zero_int, zero_int);
    let div00 = NatOps::div(d, nat_zero, nat_zero);
    let ofnat_div00 = d.of_nat(div00);
    let zero_div_lemma = {
        let name = p.nat.zero_div;
        d.const_app(name, &[nat_zero])
    }; // Eq Nat div00 nat_zero
    let ofnat_div00_eq_zero = d.nat_eq_to_int(div00, nat_zero, zero_div_lemma, &|d, x| d.of_nat(x));
    let step_refl = d.irefl(qa0); // typed (by defeq) as Eq Int qa0 ofnat_div00
    let (_, qa0_eq_zero) = d.ichain(
        qa0,
        &[(ofnat_div00, step_refl), (zero_int, ofnat_div00_eq_zero)],
    );

    // LHS: gcd(qa0,qa0) = gcd(zero,zero) = natAbs(zero) = zero.
    let g_qa0 = igcd(d, qa0, qa0);
    let step_a = icongr_nat(d, qa0, zero_int, qa0_eq_zero, &|d, x| igcd(d, x, qa0));
    let step_b = icongr_nat(d, qa0, zero_int, qa0_eq_zero, &|d, x| igcd(d, zero_int, x));
    let gzz_eq_natabs0 = d.const_app(p.gcd_zero_right, &[zero_int]); // Eq Nat (gcd 0 0) (natAbs 0)
    let natabs0 = nat_abs(d, zero_int);
    let natabs0_eq_zero = d.refl(natabs0); // typed (by defeq) as Eq Nat natabs0 nat_zero
    let g_zero_qa0 = igcd(d, zero_int, qa0);
    let g_zero_zero = igcd(d, zero_int, zero_int);
    let (lhs_final, lhs_proof) = d.chain(
        g_qa0,
        &[
            (g_zero_qa0, step_a),
            (g_zero_zero, step_b),
            (natabs0, gzz_eq_natabs0),
            (nat_zero, natabs0_eq_zero),
        ],
    );
    let _ = lhs_final;

    // RHS: div(gcd(zero,zero), natAbs zero) = div(zero, zero) = zero.
    let g00 = igcd(d, zero_int, zero_int);
    let cabs0 = nat_abs(d, zero_int);
    let rhs_start = NatOps::div(d, g00, cabs0);
    let g00_eq_zero = {
        let (_, pr) = d.chain(
            g00,
            &[(natabs0, gzz_eq_natabs0), (nat_zero, natabs0_eq_zero)],
        );
        pr
    };
    let step_r1 = NatOps::congr(d, g00, nat_zero, g00_eq_zero, &|d, x| {
        NatOps::div(d, x, cabs0)
    });
    let div_nat_zero_cabs0 = NatOps::div(d, nat_zero, cabs0);
    let step_r2 = NatOps::congr(d, cabs0, nat_zero, natabs0_eq_zero, &|d, x| {
        NatOps::div(d, nat_zero, x)
    });
    let (rhs_final, rhs_proof) = d.chain(
        rhs_start,
        &[
            (div_nat_zero_cabs0, step_r1),
            (div00, step_r2),
            (nat_zero, zero_div_lemma),
        ],
    );
    let _ = rhs_final;

    let rhs_proof_rev = d.symm(rhs_start, nat_zero, rhs_proof);
    d.trans(g_qa0, nat_zero, rhs_start, lhs_proof, rhs_proof_rev)
}

/// The nonzero-divisor case, shared by `c = ofNat (succ m)` and
/// `c = negSucc n`: given `hne : Not (Eq Int cc zero)` and
/// `one_le_cabs : Nat.le (succ zero) (natAbs cc)`, proves
/// `gcd_div_goal(a, b, cc)` by the mutual-divisibility argument described in
/// this section's module doc.
fn gcd_div_nonzero_case(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    cc: ExprId,
    hne: ExprId,
    one_le_cabs: ExprId,
) -> ExprId {
    let p = d.int();
    let dvd_ca = idvd(d, cc, a);
    let dvd_cb = idvd(d, cc, b);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let qa = d.iediv(a, cc);
    let qb = d.iediv(b, cc);
    let cabs = nat_abs(d, cc);
    let g = igcd(d, a, b);
    let hh = igcd(d, qa, qb);

    let a_eq_cqa = exact_general(d, a, cc, h1, hne); // Eq Int a (cc*qa)
    let b_eq_cqb = exact_general(d, b, cc, h2, hne); // Eq Int b (cc*qb)

    // --- C ∣ G; K := G/C with C*K = G. --------------------------------------
    let natabs_a = nat_abs(d, a);
    let natabs_b = nat_abs(d, b);
    let c_dvd_natabs_a = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[cc, a, h1]);
    let c_dvd_natabs_b = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[cc, b, h2]);
    let c_dvd_g = d.lemma(
        p.nat.dvd_gcd,
        &[cabs, natabs_a, natabs_b, c_dvd_natabs_a, c_dvd_natabs_b],
    );
    // c_dvd_g : Nat.dvd cabs (Nat.gcd natabs_a natabs_b), defeq Nat.dvd cabs g

    let kk = NatOps::div(d, g, cabs);
    let cabs_kk_eq_g = {
        let name = p.nat.div_mul_cancel_of_dvd;
        d.const_app(name, &[cabs, g, one_le_cabs, c_dvd_g])
    }; // Eq Nat (cabs*kk) g

    // --- Bézout on a, b: ofNat g = a*u + b*v = c*X, X := qa*u + qb*v. -------
    let u = d.const_app(p.gcd_a, &[a, b]);
    let vv = d.const_app(p.gcd_b, &[a, b]);
    let eq_bezout = d.lemma(p.gcd_eq_gcd_ab_witnesses, &[a, b]); // Eq Int (ofNat g) (a*u+b*v)
    let ofnat_g = d.of_nat(g);

    let au = d.imul(a, u);
    let bv = d.imul(b, vv);
    let c_qa = d.imul(cc, qa);
    let c_qb = d.imul(cc, qb);
    let c_qa_u = d.imul(c_qa, u);
    let c_qb_v = d.imul(c_qb, vv);

    let au_to_cqau = d.icongr(a, c_qa, a_eq_cqa, &|d, x| d.imul(x, u));
    let bv_to_cqbv = d.icongr(b, c_qb, b_eq_cqb, &|d, x| d.imul(x, vv));
    let step_sum1 = d.icongr(au, c_qa_u, au_to_cqau, &|d, x| d.iadd(x, bv));
    let step_sum2 = d.icongr(bv, c_qb_v, bv_to_cqbv, &|d, x| d.iadd(c_qa_u, x));

    let au_plus_bv = d.iadd(au, bv);
    let cqau_plus_bv = d.iadd(c_qa_u, bv);
    let cqau_plus_cqbv = d.iadd(c_qa_u, c_qb_v);
    let (_, sub_chained) = d.ichain(
        au_plus_bv,
        &[(cqau_plus_bv, step_sum1), (cqau_plus_cqbv, step_sum2)],
    );
    let g_eq_prod = d.itrans(ofnat_g, au_plus_bv, cqau_plus_cqbv, eq_bezout, sub_chained);

    let qa_u = d.imul(qa, u);
    let qb_v = d.imul(qb, vv);
    let c_qau2 = d.imul(cc, qa_u);
    let c_qbv2 = d.imul(cc, qb_v);
    let assoc_a = d.const_app(p.mul_assoc, &[cc, qa, u]); // Eq Int (c_qa*u) c_qau2
    let assoc_b = d.const_app(p.mul_assoc, &[cc, qb, vv]); // Eq Int (c_qb*v) c_qbv2
    let step3 = d.icongr(c_qa_u, c_qau2, assoc_a, &|d, x| d.iadd(x, c_qb_v));
    let step4 = d.icongr(c_qb_v, c_qbv2, assoc_b, &|d, x| d.iadd(c_qau2, x));
    let cqau2_plus_cqbv = d.iadd(c_qau2, c_qb_v);
    let cqau2_plus_cqbv2 = d.iadd(c_qau2, c_qbv2);
    let (_, factor_chained) = d.ichain(
        cqau_plus_cqbv,
        &[(cqau2_plus_cqbv, step3), (cqau2_plus_cqbv2, step4)],
    );

    let x_expr = d.iadd(qa_u, qb_v); // X
    let c_x = d.imul(cc, x_expr);
    let distrib = d.const_app(p.left_distrib, &[cc, qa_u, qb_v]); // Eq Int c_x cqau2_plus_cqbv2
    let distrib_rev = d.isymm(c_x, cqau2_plus_cqbv2, distrib);
    let (_, g_eq_cx) = d.ichain(
        ofnat_g,
        &[
            (cqau_plus_cqbv, g_eq_prod),
            (cqau2_plus_cqbv2, factor_chained),
            (c_x, distrib_rev),
        ],
    ); // g_eq_cx : Eq Int (ofNat g) (c*X)

    // --- natAbs both sides: g = cabs * natAbs(X). ---------------------------
    let natabs_x = nat_abs(d, x_expr);
    let natabs_cx = nat_abs(d, c_x);
    let natabs_congr = icongr_nat(d, ofnat_g, c_x, g_eq_cx, &|d, y| nat_abs(d, y));
    // natabs_congr : Eq Nat (natAbs ofnat_g) natabs_cx, defeq Eq Nat g natabs_cx
    let cabs_natabsx = NatOps::mul(d, cabs, natabs_x);
    let mul_cx_lemma = d.const_app(p.nat_abs_mul, &[cc, x_expr]); // Eq Nat natabs_cx cabs_natabsx
    let (_, g_eq_cabs_natabsx) = d.chain(
        g,
        &[(natabs_cx, natabs_congr), (cabs_natabsx, mul_cx_lemma)],
    );

    // cabs*kk = g = cabs*natAbs(X)  =>  kk = natAbs(X)  (cancel cabs).
    let cabs_kk = NatOps::mul(d, cabs, kk);
    let (_, cabs_kk_eq_cabs_natabsx) = d.chain(
        cabs_kk,
        &[(g, cabs_kk_eq_g), (cabs_natabsx, g_eq_cabs_natabsx)],
    );
    let kk_eq_natabsx = {
        let name = p.nat.mul_left_cancel_of_pos;
        d.const_app(
            name,
            &[cabs, kk, natabs_x, one_le_cabs, cabs_kk_eq_cabs_natabsx],
        )
    }; // Eq Nat kk natabs_x

    // --- Direction 1: H ∣ K. -------------------------------------------------
    let ofnat_hh = d.of_nat(hh);
    let dvd_qa = d.const_app(p.gcd_dvd_left, &[qa, qb]); // idvd(ofnat_hh, qa)
    let dvd_qb = d.const_app(p.gcd_dvd_right, &[qa, qb]); // idvd(ofnat_hh, qb)
    let dvd_qau = {
        let step = d.const_app(p.dvd_mul_right, &[qa, u]);
        d.const_app(p.dvd_trans, &[ofnat_hh, qa, qa_u, dvd_qa, step])
    };
    let dvd_qbv = {
        let step = d.const_app(p.dvd_mul_right, &[qb, vv]);
        d.const_app(p.dvd_trans, &[ofnat_hh, qb, qb_v, dvd_qb, step])
    };
    let dvd_x = d.const_app(p.dvd_add, &[ofnat_hh, qa_u, qb_v, dvd_qau, dvd_qbv]); // idvd(ofnat_hh, x_expr)
    let hh_dvd_natabsx = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[ofnat_hh, x_expr, dvd_x]);
    // hh_dvd_natabsx : Nat.dvd (natAbs ofnat_hh) natabs_x, defeq Nat.dvd hh natabs_x

    let natabsx_eq_kk = d.symm(kk, natabs_x, kk_eq_natabsx); // Eq Nat natabs_x kk
    let hh_dvd_kk = d.nat_rewrite(natabs_x, kk, natabsx_eq_kk, hh_dvd_natabsx, &|d, w| {
        d.dvd(hh, w)
    });

    // --- Direction 2: K ∣ H. -------------------------------------------------
    let up = d.const_app(p.gcd_a, &[qa, qb]);
    let vp = d.const_app(p.gcd_b, &[qa, qb]);
    let eq_bezout2 = d.lemma(p.gcd_eq_gcd_ab_witnesses, &[qa, qb]); // Eq Int (ofNat hh) (qa*u'+qb*v')

    let cc_hh = d.imul(cc, ofnat_hh);
    let qau2 = d.imul(qa, up);
    let qbv2 = d.imul(qb, vp);
    let sum2 = d.iadd(qau2, qbv2);
    let cc_sum2 = d.imul(cc, sum2);
    let cc_qau2 = d.imul(cc, qau2);
    let cc_qbv2 = d.imul(cc, qbv2);
    let distrib2 = d.const_app(p.left_distrib, &[cc, qau2, qbv2]); // Eq Int cc_sum2 (cc_qau2+cc_qbv2)
    let cc_eq_hh_to_cc_sum2 = d.icongr(ofnat_hh, sum2, eq_bezout2, &|d, x| d.imul(cc, x));
    let ccqau2_plus_ccqbv2 = d.iadd(cc_qau2, cc_qbv2);
    let (_, chain_a) = d.ichain(
        cc_hh,
        &[
            (cc_sum2, cc_eq_hh_to_cc_sum2),
            (ccqau2_plus_ccqbv2, distrib2),
        ],
    ); // chain_a : Eq Int cc_hh ccqau2_plus_ccqbv2

    let au2 = d.imul(a, up);
    let bv2 = d.imul(b, vp);
    let a_to_cqa_u = d.icongr(a, c_qa, a_eq_cqa, &|d, x| d.imul(x, up));
    let assoc_a2 = d.const_app(p.mul_assoc, &[cc, qa, up]); // Eq Int (c_qa*up) cc_qau2
    let cqa_up = d.imul(c_qa, up);
    let (_, au2_eq_ccqau2) = d.ichain(au2, &[(cqa_up, a_to_cqa_u), (cc_qau2, assoc_a2)]);

    let b_to_cqb_v = d.icongr(b, c_qb, b_eq_cqb, &|d, x| d.imul(x, vp));
    let assoc_b2 = d.const_app(p.mul_assoc, &[cc, qb, vp]); // Eq Int (c_qb*vp) cc_qbv2
    let cqb_vp = d.imul(c_qb, vp);
    let (_, bv2_eq_ccqbv2) = d.ichain(bv2, &[(cqb_vp, b_to_cqb_v), (cc_qbv2, assoc_b2)]);

    let step_s1 = d.icongr(au2, cc_qau2, au2_eq_ccqau2, &|d, x| d.iadd(x, bv2));
    let step_s2 = d.icongr(bv2, cc_qbv2, bv2_eq_ccqbv2, &|d, x| d.iadd(cc_qau2, x));
    let au2_plus_bv2 = d.iadd(au2, bv2);
    let ccqau2_plus_bv2 = d.iadd(cc_qau2, bv2);
    let (_, sum_chain2) = d.ichain(
        au2_plus_bv2,
        &[(ccqau2_plus_bv2, step_s1), (ccqau2_plus_ccqbv2, step_s2)],
    );
    let sum_chain2_rev = d.isymm(au2_plus_bv2, ccqau2_plus_ccqbv2, sum_chain2);
    let cc_hh_eq_sum = d.itrans(
        cc_hh,
        ccqau2_plus_ccqbv2,
        au2_plus_bv2,
        chain_a,
        sum_chain2_rev,
    );
    // cc_hh_eq_sum : Eq Int cc_hh au2_plus_bv2

    let dvd_a = d.const_app(p.gcd_dvd_left, &[a, b]); // idvd(ofnat_g, a)
    let dvd_b = d.const_app(p.gcd_dvd_right, &[a, b]); // idvd(ofnat_g, b)
    let dvd_au2 = {
        let step = d.const_app(p.dvd_mul_right, &[a, up]);
        d.const_app(p.dvd_trans, &[ofnat_g, a, au2, dvd_a, step])
    };
    let dvd_bv2 = {
        let step = d.const_app(p.dvd_mul_right, &[b, vp]);
        d.const_app(p.dvd_trans, &[ofnat_g, b, bv2, dvd_b, step])
    };
    let dvd_sum2 = d.const_app(p.dvd_add, &[ofnat_g, au2, bv2, dvd_au2, dvd_bv2]); // idvd(ofnat_g, au2_plus_bv2)
    let sum_eq_cchh = d.isymm(cc_hh, au2_plus_bv2, cc_hh_eq_sum); // Eq Int au2_plus_bv2 cc_hh
    let dvd_cchh = d.int_eq_rewrite(au2_plus_bv2, cc_hh, sum_eq_cchh, dvd_sum2, &|d, y| {
        idvd(d, ofnat_g, y)
    }); // idvd(ofnat_g, cc_hh)

    let g_dvd_natabs_cchh = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[ofnat_g, cc_hh, dvd_cchh]);
    // g_dvd_natabs_cchh : Nat.dvd (natAbs ofnat_g) (natAbs cc_hh), defeq Nat.dvd g (natAbs cc_hh)
    let natabs_cchh = nat_abs(d, cc_hh);
    let mul_cchh_lemma = d.const_app(p.nat_abs_mul, &[cc, ofnat_hh]); // Eq Nat natabs_cchh (cabs*natAbs(ofnat_hh))
    let natabs_ofnat_hh = nat_abs(d, ofnat_hh);
    let cabs_natabshh = NatOps::mul(d, cabs, natabs_ofnat_hh);
    let g_dvd_cabs_natabshh = d.nat_rewrite(
        natabs_cchh,
        cabs_natabshh,
        mul_cchh_lemma,
        g_dvd_natabs_cchh,
        &|d, w| d.dvd(g, w),
    );
    // g_dvd_cabs_natabshh : Nat.dvd g cabs_natabshh, defeq Nat.dvd g (cabs*hh)
    // (`natAbs (ofNat hh) ≡ hh` is pure `iota`, but `g ≡ cabs*kk` is a PROVED
    // fact, not defeq -- rewrite the divisor explicitly via `cabs_kk_eq_g`.)
    let g_eq_cabs_kk = d.symm(cabs_kk, g, cabs_kk_eq_g); // Eq Nat g cabs_kk
    let cabs_kk_dvd_cabs_natabshh =
        d.nat_rewrite(g, cabs_kk, g_eq_cabs_kk, g_dvd_cabs_natabshh, &|d, w| {
            d.dvd(w, cabs_natabshh)
        });
    // cabs_kk_dvd_cabs_natabshh : Nat.dvd cabs_kk cabs_natabshh, defeq Nat.dvd (cabs*kk) (cabs*hh)
    let kk_dvd_hh = cancel_dvd_of_pos(d, cabs, kk, hh, one_le_cabs, cabs_kk_dvd_cabs_natabshh);

    // --- Antisymmetry closes it: hh = kk = g / cabs. ------------------------
    let hh_eq_kk = d.lemma(p.nat.dvd_antisymm, &[hh, kk, hh_dvd_kk, kk_dvd_hh]);

    let with_h2 = d.lam_fv(h2_fv, dvd_cb, hh_eq_kk);
    d.lam_fv(h1_fv, dvd_ca, with_h2)
}

/// From `x`, `cc`, `dvd_c_x : idvd(cc, x)` and `hne : Not (Eq Int cc zero)`,
/// derive `Eq Int x (cc * x.ediv cc)` -- exact division, sign-general
/// analogue of [`declare_gcd_div_gcd_div_gcd`]'s local `exact` closure, via
/// [`super::dvd::declare_emod_eq_zero_iff_dvd_general`] in place of the
/// positive-only bridge.
fn exact_general(
    d: &mut IntDev<'_>,
    x: ExprId,
    cc: ExprId,
    dvd_c_x: ExprId,
    hne: ExprId,
) -> ExprId {
    let p = d.int();
    let ediv_xc = d.iediv(x, cc);
    let emod_xc = d.iemod(x, cc);
    let zero_i = d.izero();
    let zero_eq_ty = d.ieq(emod_xc, zero_i);
    let dvd_ty = idvd(d, cc, x);
    let iff_xc = d.const_app(p.emod_eq_zero_iff_dvd_general, &[x, cc, hne]);
    let mpr = d.const_app(p.logic.iff_mpr, &[zero_eq_ty, dvd_ty, iff_xc]);
    let emod_eq_zero = d.apply(mpr, &[dvd_c_x]);

    let mul_q = d.imul(cc, ediv_xc);
    let sum_with_emod = d.iadd(mul_q, emod_xc);
    let full_eq = d.const_app(p.ediv_add_emod, &[x, cc]); // Eq(sum_with_emod, x)
    let full_eq_rev = d.isymm(sum_with_emod, x, full_eq); // Eq(x, sum_with_emod)
    let sum_with_zero = d.iadd(mul_q, zero_i);
    let step = d.icongr(emod_xc, zero_i, emod_eq_zero, &|d, y| d.iadd(mul_q, y));
    let add_zero_q = d.const_app(p.add_zero, &[mul_q]); // Eq(sum_with_zero, mul_q)
    let (_, chained) = d.ichain(sum_with_emod, &[(sum_with_zero, step), (mul_q, add_zero_q)]);
    d.itrans(x, sum_with_emod, mul_q, full_eq_rev, chained) // Eq(x, cc*(x/cc))
}

/// `Int.gcd_div : ∀ a b c, c ∣ a → c ∣ b →
/// Eq Nat (gcd (a.ediv c) (b.ediv c)) (Nat.div (gcd a b) (natAbs c))`.
///
/// # Errors
///
/// Returns the trusted kernel gate's rejection if the constructed term does
/// not check.
pub(super) fn declare_gcd_div(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_div, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let stmt = gcd_div_goal(d, a, b, c);
        let proof = case_split(
            d,
            &[c],
            &|d, args| gcd_div_goal(d, a, b, args[0]),
            &|d, branches| {
                let (shape, n) = branches[0];
                match shape {
                    Shape::NegSucc => {
                        let cc = d.neg_succ(n);
                        let zero_int = d.izero();
                        let eq_ty = d.ieq(cc, zero_int);
                        let h_fv = d.fresh_fvar();
                        let h = d.kernel().fvar(h_fv);
                        let false_proof = super::decide::discriminate(d, cc, zero_int, h, false);
                        let hne = d.lam_fv(h_fv, eq_ty, false_proof);
                        let one_le_cabs = super::division::positive_of_succ(d, n);
                        gcd_div_nonzero_case(d, a, b, cc, hne, one_le_cabs)
                    }
                    Shape::OfNat => d.induct(
                        &|d, nn| {
                            let cc = d.of_nat(nn);
                            gcd_div_goal(d, a, b, cc)
                        },
                        &|d| gcd_div_zero_case(d, a, b),
                        &|d, m, _ih| {
                            let succ_m = d.succ(m);
                            let cc = d.of_nat(succ_m);
                            let one_le_cabs = super::division::positive_of_succ(d, m);
                            let hne = super::dvd::ne_zero_of_pos(d, cc, one_le_cabs);
                            gcd_div_nonzero_case(d, a, b, cc, hne, one_le_cabs)
                        },
                        n,
                    ),
                }
            },
        );
        (stmt, proof)
    })?;
    Ok(())
}
