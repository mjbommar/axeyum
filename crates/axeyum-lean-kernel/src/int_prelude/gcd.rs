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
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::{Branch, IntDev, Shape, case_split};

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
// General `Int.neg` ring facts this development did not yet need:
// `neg_mul`, `mul_neg`, `neg_neg`. Not declared as public theorems (nothing
// else needs them yet); kept as private proof-term builders.
// ---------------------------------------------------------------------------

/// `Eq Int (neg (neg x)) x`, for any `x`.
///
/// `neg (neg one) = one` holds by `rfl` (two `Int.rec` computations on the
/// concrete literal `1`, no case split needed since neither reduction depends
/// on a variable), and from there `neg (neg x) = (-1)*(-1)*x = 1*x = x` by
/// `neg_one_mul`/`mul_assoc`/`one_mul` alone.
fn neg_neg(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
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
fn neg_mul(d: &mut IntDev<'_>, a: ExprId, c: ExprId) -> ExprId {
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
