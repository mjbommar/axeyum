//! `ml430` mirrors for the ℤ divisibility/gcd/`ModEq` family that `gcd.rs`,
//! `dvd.rs`, `modeq.rs` and `modeq_family.rs` did not already close.
//!
//! Every declaration here is a genuine composition of ALREADY-PROVED
//! machinery from those four modules — no new base algebra, no new case
//! splits over `Int.rec`/`Nat.rec`. The two families:
//!
//! ## `Int.gcd`'s `Nat`-typed divisor (Mathlib's actual `Int.dvd_gcd`)
//!
//! `int_prelude/gcd.rs`'s existing `p.dvd_gcd` is Mathlib's
//! `Int.dvd_coe_gcd` (an **Int**-typed divisor `c`, with the coercion sitting
//! around `a.gcd b` on the conclusion's right): `c ∣ a → c ∣ b →
//! c ∣ ↑(a.gcd b)`. Mathlib's `Int.dvd_gcd` is a different, Nat-typed-divisor
//! statement — `c : ℕ`, hypotheses `↑c ∣ a`/`↑c ∣ b`, conclusion
//! `c ∣ a.gcd b` (a bare `Nat.dvd`, no coercion on the conclusion at all).
//! [`declare_dvd_gcd_nat`] builds that one directly from
//! `nat_abs_dvd_nat_abs_of_dvd` (the cast `natAbs (ofNat c) ≡ c` erases by
//! `rfl`, so no bridge lemma is needed for the cast itself) and
//! `Nat.dvd_gcd`. [`declare_dvd_gcd_nat_iff`] is the iff form, adding the
//! reverse direction via `Nat.gcd_dvd_left`/`Nat.gcd_dvd_right` and
//! `Nat.dvd_trans`. [`declare_dvd_coe_gcd_iff`] is the analogous iff for the
//! *coe* form (`c : ℤ`), built from `p.dvd_gcd`/`gcd_dvd_left`/
//! `gcd_dvd_right`/`dvd_trans`.
//!
//! ## `Int.ediv_gcd_ne_zero_{of_ne_zero_left,if_ne_zero_right}`
//!
//! `b ≠ 0 → b / ↑(a.gcd b) ≠ 0` (and the mirrored `a` form). The argument:
//! `c := ofNat (gcd a b)` divides the numerator (`gcd_dvd_left`/
//! `gcd_dvd_right`), and `c ≠ 0` follows from the numerator being nonzero
//! (`gcd_dvd_left`/`_right` plus [`zero_dvd_elim`] gives the contrapositive:
//! if `c = 0` then the dividend is `0`). With `c ≠ 0` and `c ∣ x`, exact
//! division (`exact_general`, a local copy of `gcd.rs`'s private helper of
//! the same name — see its own doc for why each file keeps its own copy)
//! gives `x = c * (x.ediv c)`; substituting a hypothetical
//! `x.ediv c = 0` collapses the right side to `c * 0 = 0` (`Int.mul_zero`),
//! contradicting `x ≠ 0`.
//!
//! ## `Int.ModEq`'s unconditional additive family
//!
//! `modeq.rs`'s `mod_eq_add_right`/`mod_eq_add_left`/`mod_eq_add_left_cancel`
//! are already UNCONDITIONAL in the modulus (no `0 < n` hypothesis) — see
//! their own doc comments for why the old positivity-scoped proofs were
//! never load-bearing. That is exactly what the remaining Mathlib
//! `Int.ModEq.add*`/`.dvd`/`.eq` ledger rows need, and none of them needs a
//! new divisibility argument, only composition:
//!
//! - [`declare_mod_eq_add`] (`Int.ModEq.add`): `add_right` then `add_left`,
//!   chained by `ModEq.trans`.
//! - [`declare_mod_eq_add_right_cancel_single`] (Mathlib's
//!   `Int.ModEq.add_right_cancel'`, the single-`c` cancellation): rewrite
//!   `a+c`/`b+c` to `c+a`/`c+b` via `Int.add_comm`, then
//!   `mod_eq_add_left_cancel`.
//! - [`declare_mod_eq_add_left_cancel_general`] / **`_right_cancel_general`**
//!   (Mathlib's 4-variable `Int.ModEq.add_left_cancel`/
//!   `.add_right_cancel`): shift one hypothesis by the other's un-cancelled
//!   term, `trans` against the second hypothesis, then cancel with
//!   `mod_eq_add_left_cancel`/[`declare_mod_eq_add_right_cancel_single`].
//! - [`declare_mod_eq_dvd`] (`Int.ModEq.dvd`): a direct wrapper around
//!   `modeq.rs`'s already-unconditional `modeq_to_dvd` bridge, which was
//!   built as a private step and never itself exposed as a declared
//!   theorem.
//! - [`declare_mod_eq_emod_eq`] (`Int.ModEq.eq`, i.e. `a ≡ b [ZMOD n] →
//!   a % n = b % n`): `Int.ModEq n a b` **is defined** as
//!   `Eq Int (emod a n) (emod b n)` (`modeq.rs`'s `declare_modeq_definition`),
//!   so the hypothesis already has exactly the goal's type up to unfolding
//!   one `Definition` — the proof is the hypothesis itself.
//!
//! None of these needed a new fuel/recursion argument or a new base
//! algebraic identity; every step is `dvd_trans`/`mod_eq_trans`/
//! `mod_eq_symm`/`Int.add_comm` composition over lemmas `gcd.rs`/`dvd.rs`/
//! `modeq.rs` already proved and exposed as `IntPrelude` fields.

use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::modeq::{dvd_to_modeq, imodeq, modeq_to_dvd};
use super::ops::IntDev;

// ---------------------------------------------------------------------------
// Small local term-building helpers (each file in this development keeps its
// own thin copies of these -- see `dvd.rs`'s and `gcd.rs`'s module docs for
// why they are not shared).
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

/// Eliminate `witness : Exists Int predicate` into `target`, given
/// `minor : ∀ (u : Int), predicate u → target`. Local copy of the same
/// combinator `gcd.rs`/`euler.rs`/`euler_totient.rs`/`crt.rs` each keep.
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

/// `Eq Int x zero` from `h_dvd : Int.dvd zero_int x`. Local copy of
/// `gcd.rs`'s private `zero_dvd_elim` (same construction: any witness to
/// `x = zero_int * c` forces `x = zero_int` via `Int.mul_comm`/`Int.mul_zero`).
fn zero_dvd_elim(d: &mut IntDev<'_>, x: ExprId, h_dvd: ExprId) -> ExprId {
    let p = d.int();
    let zero_int = d.izero();
    let pred = super::dvd::dvd_predicate(d, zero_int, x);
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

/// From `x`, `cc`, `dvd_c_x : idvd(cc, x)` and `hne : Not (Eq Int cc zero)`,
/// derive `Eq Int x (cc * x.ediv cc)`. Local copy of `gcd.rs`'s private
/// `exact_general` (same construction, via
/// `dvd::declare_emod_eq_zero_iff_dvd_general`).
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
    let dvd_ty = super::dvd::idvd(d, cc, x);
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

/// A theorem with an explicit, possibly-mixed, list of binder TYPES (unlike
/// `IntDev::int_theorem`, which forces every binder to `Int`). Needed for the
/// `Nat`-typed-divisor `Int.dvd_gcd`/`Int.dvd_gcd_iff` mirrors, whose divisor
/// `c` is `ℕ`-typed while `a`, `b` stay `ℤ`.
fn theorem_mixed(
    d: &mut IntDev<'_>,
    name: crate::NameId,
    arg_tys: &[ExprId],
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) -> Result<(), KernelError> {
    let fvs: Vec<u64> = arg_tys.iter().map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
    let (stmt, proof) = build(d, &vars);
    let mut ty = stmt;
    let mut value = proof;
    for (&fv, &t) in fvs.iter().zip(arg_tys.iter()).rev() {
        ty = d.pi_fv(fv, t, ty);
        value = d.lam_fv(fv, t, value);
    }
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.dvd_gcd` / `Int.dvd_gcd_iff` (Nat-typed divisor) and
// `Int.dvd_coe_gcd_iff` (Int-typed divisor).
// ---------------------------------------------------------------------------

/// `dvd_gcd_nat : ∀ (a b : Int) (c : Nat), ofNat c ∣ a → ofNat c ∣ b →
/// c ∣ gcd a b` — Mathlib's actual `Int.dvd_gcd` (the `Nat`-typed-divisor
/// form; `gcd.rs`'s existing `p.dvd_gcd` is the *coe* form, Mathlib's
/// `Int.dvd_coe_gcd`).
///
/// `natAbs (ofNat c) ≡ c` by `rfl` (`nat_abs.rs`'s computation rule), so
/// `nat_abs_dvd_nat_abs_of_dvd` applied to each hypothesis already produces
/// exactly `Nat.dvd c (natAbs a)`/`Nat.dvd c (natAbs b)` up to that
/// defeq -- no cast bridge lemma is needed. `Nat.dvd_gcd` closes it, and its
/// conclusion `Nat.dvd c (Nat.gcd (natAbs a) (natAbs b))` is defeq to the
/// stated goal `Nat.dvd c (gcd a b)` by `Int.gcd`'s own definition.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_dvd_gcd_nat(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();
    let name = p.dvd_gcd_nat;
    theorem_mixed(d, name, &[int_ty, int_ty, nat_ty], &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let of_c = d.of_nat(c);
        let h1_ty = super::dvd::idvd(d, of_c, a);
        let h2_ty = super::dvd::idvd(d, of_c, b);
        let g = igcd(d, a, b);
        let goal = d.dvd(c, g);
        let inner = d.arrow(h2_ty, goal);
        let stmt = d.arrow(h1_ty, inner);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let p = d.int();
        let n1 = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_c, a, h1]);
        let n2 = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_c, b, h2]);
        let big_a = nat_abs(d, a);
        let big_b = nat_abs(d, b);
        let dvd_gcd_nat = d.lemma(p.nat.dvd_gcd, &[c, big_a, big_b]);
        let result = d.apply(dvd_gcd_nat, &[n1, n2]);

        let with_h2 = d.lam_fv(h2_fv, h2_ty, result);
        let proof = d.lam_fv(h1_fv, h1_ty, with_h2);
        (stmt, proof)
    })
}

/// `dvd_gcd_nat_iff : ∀ (a b : Int) (c : Nat),
/// Iff (c ∣ gcd a b) (And (ofNat c ∣ a) (ofNat c ∣ b))` — Mathlib's
/// `Int.dvd_gcd_iff`.
///
/// `mp`: `Nat.gcd_dvd_left`/`Nat.gcd_dvd_right` (up to the same `Int.gcd`
/// unfold `declare_dvd_gcd_nat` uses) plus `Nat.dvd_trans` give
/// `Nat.dvd c (natAbs a)`/`Nat.dvd c (natAbs b)`, and
/// `dvd_of_nat_abs_dvd` lifts each back to `ofNat c ∣ a`/`ofNat c ∣ b`
/// (`natAbs (ofNat c) ≡ c` again erasing the cast by `rfl`). `mpr` is
/// exactly [`declare_dvd_gcd_nat`]'s body.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_dvd_gcd_nat_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();
    let name = p.dvd_gcd_nat_iff;
    theorem_mixed(d, name, &[int_ty, int_ty, nat_ty], &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let p = d.int();
        let of_c = d.of_nat(c);
        let g = igcd(d, a, b);
        let lhs = d.dvd(c, g);
        let ca_ty = super::dvd::idvd(d, of_c, a);
        let cb_ty = super::dvd::idvd(d, of_c, b);
        let rhs = d.and(ca_ty, cb_ty);
        let iff_ty = {
            let name = p.logic.iff;
            d.const_app(name, &[lhs, rhs])
        };

        let big_a = nat_abs(d, a);
        let big_b = nat_abs(d, b);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let gdl = d.const_app(p.nat.gcd_dvd_left, &[big_a, big_b]); // Nat.dvd g big_a
            let gdr = d.const_app(p.nat.gcd_dvd_right, &[big_a, big_b]); // Nat.dvd g big_b
            let t1 = d.lemma(p.nat.dvd_trans, &[c, g, big_a]);
            let n1 = d.apply(t1, &[h, gdl]); // Nat.dvd c big_a
            let t2 = d.lemma(p.nat.dvd_trans, &[c, g, big_b]);
            let n2 = d.apply(t2, &[h, gdr]); // Nat.dvd c big_b
            let lift1 = d.const_app(p.dvd_of_nat_abs_dvd, &[of_c, a, n1]);
            let lift2 = d.const_app(p.dvd_of_nat_abs_dvd, &[of_c, b, n2]);
            let and_proof = d.const_app(p.logic.and_intro, &[ca_ty, cb_ty, lift1, lift2]);
            d.lam_fv(h_fv, lhs, and_proof)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let ha = d.and_left(ca_ty, cb_ty, h);
            let hb = d.and_right(ca_ty, cb_ty, h);
            let n1 = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_c, a, ha]);
            let n2 = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_c, b, hb]);
            let dvd_gcd_nat = d.lemma(p.nat.dvd_gcd, &[c, big_a, big_b]);
            let result = d.apply(dvd_gcd_nat, &[n1, n2]);
            d.lam_fv(h_fv, rhs, result)
        };
        let iff_proof = d.const_app(p.logic.iff_intro, &[lhs, rhs, mp, mpr]);
        (iff_ty, iff_proof)
    })
}

/// `dvd_coe_gcd_iff : ∀ (a b c : Int),
/// Iff (c ∣ ofNat (gcd a b)) (And (c ∣ a) (c ∣ b))` — Mathlib's
/// `Int.dvd_coe_gcd_iff`, the *coe* companion to [`declare_dvd_gcd_nat_iff`].
///
/// `mp`: `dvd_trans` against `gcd_dvd_left`/`gcd_dvd_right`. `mpr`: exactly
/// `gcd.rs`'s existing `p.dvd_gcd` (Mathlib's `Int.dvd_coe_gcd`) fed the two
/// `And` components.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_dvd_coe_gcd_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_coe_gcd_iff, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let p = d.int();
        let g = igcd(d, a, b);
        let of_g = d.of_nat(g);
        let lhs = super::dvd::idvd(d, c, of_g);
        let ca_ty = super::dvd::idvd(d, c, a);
        let cb_ty = super::dvd::idvd(d, c, b);
        let rhs = d.and(ca_ty, cb_ty);
        let iff_ty = {
            let name = p.logic.iff;
            d.const_app(name, &[lhs, rhs])
        };

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let gdl = d.const_app(p.gcd_dvd_left, &[a, b]); // idvd(of_g, a)
            let gdr = d.const_app(p.gcd_dvd_right, &[a, b]); // idvd(of_g, b)
            let t1 = d.lemma(p.dvd_trans, &[c, of_g, a]);
            let ca = d.apply(t1, &[h, gdl]);
            let t2 = d.lemma(p.dvd_trans, &[c, of_g, b]);
            let cb = d.apply(t2, &[h, gdr]);
            let and_proof = d.const_app(p.logic.and_intro, &[ca_ty, cb_ty, ca, cb]);
            d.lam_fv(h_fv, lhs, and_proof)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let ha = d.and_left(ca_ty, cb_ty, h);
            let hb = d.and_right(ca_ty, cb_ty, h);
            let dvd_gcd = d.lemma(p.dvd_gcd, &[c, a, b]);
            let result = d.apply(dvd_gcd, &[ha, hb]);
            d.lam_fv(h_fv, rhs, result)
        };
        let iff_proof = d.const_app(p.logic.iff_intro, &[lhs, rhs, mp, mpr]);
        (iff_ty, iff_proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.ediv_gcd_ne_zero_{of_ne_zero_left,if_ne_zero_right}`.
// ---------------------------------------------------------------------------

/// `ediv_gcd_ne_zero_of_ne_zero_left : ∀ a b, Not (Eq Int a zero) →
/// Not (Eq Int (a.ediv (ofNat (gcd a b))) zero)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_ediv_gcd_ne_zero_of_ne_zero_left(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.ediv_gcd_ne_zero_of_ne_zero_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let p = d.int();
        let g = igcd(d, a, b);
        let c = d.of_nat(g);
        let zero_i = d.izero();
        let a_eq_zero_ty = d.ieq(a, zero_i);
        let a_ne_zero_ty = d.not(a_eq_zero_ty);
        let ediv_ac = d.iediv(a, c);
        let ediv_ac_eq_zero_ty = d.ieq(ediv_ac, zero_i);
        let concl = d.not(ediv_ac_eq_zero_ty);
        let stmt = d.arrow(a_ne_zero_ty, concl);

        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);

        let dvd_c_a = d.const_app(p.gcd_dvd_left, &[a, b]); // idvd(c, a)

        let c_ne_zero = {
            let hcz_fv = d.fresh_fvar();
            let hcz = d.kernel().fvar(hcz_fv);
            let hcz_ty = d.ieq(c, zero_i);
            let motive = |d: &mut IntDev<'_>, t: ExprId| super::dvd::idvd(d, t, a);
            let dvd_zero_a = d.int_eq_rewrite(c, zero_i, hcz, dvd_c_a, &motive);
            let a_eq_zero = zero_dvd_elim(d, a, dvd_zero_a);
            let false_proof = d.apply(ha, &[a_eq_zero]);
            d.lam_fv(hcz_fv, hcz_ty, false_proof)
        };

        let a_eq = exact_general(d, a, c, dvd_c_a, c_ne_zero); // Eq(a, c*ediv_ac)

        let not_ediv_zero = {
            let hz_fv = d.fresh_fvar();
            let hz = d.kernel().fvar(hz_fv);
            let hz_ty = d.ieq(ediv_ac, zero_i);
            let mul_q = d.imul(c, ediv_ac);
            let mul_zero_c = d.imul(c, zero_i);
            let step = d.icongr(ediv_ac, zero_i, hz, &|d, t| d.imul(c, t));
            let mz = d.const_app(p.mul_zero, &[c]); // Eq(mul_zero_c, zero_i)
            let (_, chained) = d.ichain(mul_q, &[(mul_zero_c, step), (zero_i, mz)]);
            let a_eq_zero = d.itrans(a, mul_q, zero_i, a_eq, chained);
            let false_proof = d.apply(ha, &[a_eq_zero]);
            d.lam_fv(hz_fv, hz_ty, false_proof)
        };

        let proof = d.lam_fv(ha_fv, a_ne_zero_ty, not_ediv_zero);
        (stmt, proof)
    })?;
    Ok(())
}

/// `ediv_gcd_ne_zero_if_ne_zero_right : ∀ a b, Not (Eq Int b zero) →
/// Not (Eq Int (b.ediv (ofNat (gcd a b))) zero)` -- the mirror of
/// [`declare_ediv_gcd_ne_zero_of_ne_zero_left`] against `gcd_dvd_right`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_ediv_gcd_ne_zero_if_ne_zero_right(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.ediv_gcd_ne_zero_if_ne_zero_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let p = d.int();
        let g = igcd(d, a, b);
        let c = d.of_nat(g);
        let zero_i = d.izero();
        let b_eq_zero_ty = d.ieq(b, zero_i);
        let b_ne_zero_ty = d.not(b_eq_zero_ty);
        let ediv_bc = d.iediv(b, c);
        let ediv_bc_eq_zero_ty = d.ieq(ediv_bc, zero_i);
        let concl = d.not(ediv_bc_eq_zero_ty);
        let stmt = d.arrow(b_ne_zero_ty, concl);

        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);

        let dvd_c_b = d.const_app(p.gcd_dvd_right, &[a, b]); // idvd(c, b)

        let c_ne_zero = {
            let hcz_fv = d.fresh_fvar();
            let hcz = d.kernel().fvar(hcz_fv);
            let hcz_ty = d.ieq(c, zero_i);
            let motive = |d: &mut IntDev<'_>, t: ExprId| super::dvd::idvd(d, t, b);
            let dvd_zero_b = d.int_eq_rewrite(c, zero_i, hcz, dvd_c_b, &motive);
            let b_eq_zero = zero_dvd_elim(d, b, dvd_zero_b);
            let false_proof = d.apply(hb, &[b_eq_zero]);
            d.lam_fv(hcz_fv, hcz_ty, false_proof)
        };

        let b_eq = exact_general(d, b, c, dvd_c_b, c_ne_zero); // Eq(b, c*ediv_bc)

        let not_ediv_zero = {
            let hz_fv = d.fresh_fvar();
            let hz = d.kernel().fvar(hz_fv);
            let hz_ty = d.ieq(ediv_bc, zero_i);
            let mul_q = d.imul(c, ediv_bc);
            let mul_zero_c = d.imul(c, zero_i);
            let step = d.icongr(ediv_bc, zero_i, hz, &|d, t| d.imul(c, t));
            let mz = d.const_app(p.mul_zero, &[c]);
            let (_, chained) = d.ichain(mul_q, &[(mul_zero_c, step), (zero_i, mz)]);
            let b_eq_zero = d.itrans(b, mul_q, zero_i, b_eq, chained);
            let false_proof = d.apply(hb, &[b_eq_zero]);
            d.lam_fv(hz_fv, hz_ty, false_proof)
        };

        let proof = d.lam_fv(hb_fv, b_ne_zero_ty, not_ediv_zero);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.ModEq`'s remaining unconditional additive family, plus `.dvd`/`.eq`.
// ---------------------------------------------------------------------------

/// `mod_eq_add : ∀ n a b c e, ModEq n a b → ModEq n c e →
/// ModEq n (a+c) (b+e)` -- Mathlib's `Int.ModEq.add`, UNCONDITIONAL in `n`.
///
/// `add_right` scales the first hypothesis by `c` on the right, `add_left`
/// scales the second by `b` on the left, and `mod_eq_trans` chains the two
/// results (`ModEq n (a+c) (b+c)` then `ModEq n (b+c) (b+e)`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_eq_add(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add, 5, &|d, v| {
        let (n, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let p = d.int();
        let modeq_ab = imodeq(d, n, a, b);
        let modeq_ce = imodeq(d, n, c, e);
        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);
        let be = d.iadd(b, e);
        let concl = imodeq(d, n, ac, be);
        let inner_arrow = d.arrow(modeq_ce, concl);
        let stmt = d.arrow(modeq_ab, inner_arrow);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let step1 = d.const_app(p.mod_eq_add_right, &[n, a, b, c, h1]); // ModEq n (a+c)(b+c)
        let step2 = d.const_app(p.mod_eq_add_left, &[n, c, e, b, h2]); // ModEq n (b+c)(b+e)
        let result = d.const_app(p.mod_eq_trans, &[n, ac, bc, be, step1, step2]);

        let with_h2 = d.lam_fv(h2_fv, modeq_ce, result);
        let proof = d.lam_fv(h1_fv, modeq_ab, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

/// `mod_eq_add_right_cancel : ∀ n a b c, ModEq n (a+c) (b+c) → ModEq n a b`
/// -- Mathlib's `Int.ModEq.add_right_cancel'` (the single-`c` cancellation),
/// UNCONDITIONAL in `n`.
///
/// Rewrite `a+c`/`b+c` to `c+a`/`c+b` via `Int.add_comm`, then
/// `mod_eq_add_left_cancel`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_eq_add_right_cancel_single(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_right_cancel, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let p = d.int();
        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);
        let modeq_acbc = imodeq(d, n, ac, bc);
        let modeq_ab = imodeq(d, n, a, b);
        let stmt = d.arrow(modeq_acbc, modeq_ab);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let ca = d.iadd(c, a);
        let cb = d.iadd(c, b);
        let eq1 = d.const_app(p.add_comm, &[a, c]); // Eq(ac, ca)
        let step1 = d.int_eq_rewrite(ac, ca, eq1, h, &|d, x| imodeq(d, n, x, bc));
        let eq2 = d.const_app(p.add_comm, &[b, c]); // Eq(bc, cb)
        let step2 = d.int_eq_rewrite(bc, cb, eq2, step1, &|d, x| imodeq(d, n, ca, x));

        let result = d.const_app(p.mod_eq_add_left_cancel, &[n, a, b, c, step2]);
        let proof = d.lam_fv(h_fv, modeq_acbc, result);
        (stmt, proof)
    })?;
    Ok(())
}

/// `mod_eq_add_left_cancel_general : ∀ n a b c e, ModEq n a b →
/// ModEq n (a+c) (b+e) → ModEq n c e` -- Mathlib's 4-variable
/// `Int.ModEq.add_left_cancel`, UNCONDITIONAL in `n`.
///
/// Scale the first hypothesis on the right by `c` (`ModEq n (a+c) (b+c)`),
/// flip it, chain with the second hypothesis to get `ModEq n (b+c) (b+e)`,
/// then cancel `b` on the left.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_eq_add_left_cancel_general(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_left_cancel_general, 5, &|d, v| {
        let (n, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let p = d.int();
        let modeq_ab = imodeq(d, n, a, b);
        let ac = d.iadd(a, c);
        let be = d.iadd(b, e);
        let modeq_acbe = imodeq(d, n, ac, be);
        let modeq_ce = imodeq(d, n, c, e);
        let inner_arrow = d.arrow(modeq_acbe, modeq_ce);
        let stmt = d.arrow(modeq_ab, inner_arrow);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let bc = d.iadd(b, c);
        let step1 = d.const_app(p.mod_eq_add_right, &[n, a, b, c, h1]); // ModEq n (a+c)(b+c)
        let step1_symm = d.const_app(p.mod_eq_symm, &[n, ac, bc, step1]); // ModEq n (b+c)(a+c)
        let step2 = d.const_app(p.mod_eq_trans, &[n, bc, ac, be, step1_symm, h2]); // ModEq n (b+c)(b+e)
        let result = d.const_app(p.mod_eq_add_left_cancel, &[n, c, e, b, step2]);

        let with_h2 = d.lam_fv(h2_fv, modeq_acbe, result);
        let proof = d.lam_fv(h1_fv, modeq_ab, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

/// `mod_eq_add_right_cancel_general : ∀ n a b c e, ModEq n c e →
/// ModEq n (a+c) (b+e) → ModEq n a b` -- Mathlib's 4-variable
/// `Int.ModEq.add_right_cancel`, UNCONDITIONAL in `n`.
///
/// Mirrors [`declare_mod_eq_add_left_cancel_general`]: scale the first
/// hypothesis on the left by `a`, flip, chain with the second hypothesis,
/// then cancel `d` (here `e`) on the right via
/// [`declare_mod_eq_add_right_cancel_single`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_eq_add_right_cancel_general(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_right_cancel_general, 5, &|d, v| {
        let (n, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let p = d.int();
        let modeq_ce = imodeq(d, n, c, e);
        let ac = d.iadd(a, c);
        let be = d.iadd(b, e);
        let modeq_acbe = imodeq(d, n, ac, be);
        let modeq_ab = imodeq(d, n, a, b);
        let inner_arrow = d.arrow(modeq_acbe, modeq_ab);
        let stmt = d.arrow(modeq_ce, inner_arrow);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let ae = d.iadd(a, e);
        let step1 = d.const_app(p.mod_eq_add_left, &[n, c, e, a, h1]); // ModEq n (a+c)(a+e)
        let step1_symm = d.const_app(p.mod_eq_symm, &[n, ac, ae, step1]); // ModEq n (a+e)(a+c)
        let step2 = d.const_app(p.mod_eq_trans, &[n, ae, ac, be, step1_symm, h2]); // ModEq n (a+e)(b+e)
        let result = d.const_app(p.mod_eq_add_right_cancel, &[n, a, b, e, step2]);

        let with_h2 = d.lam_fv(h2_fv, modeq_acbe, result);
        let proof = d.lam_fv(h1_fv, modeq_ce, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

/// `mod_eq_dvd : ∀ n a b, ModEq n a b → n ∣ (b - a)` -- Mathlib's
/// `Int.ModEq.dvd`, UNCONDITIONAL in `n`. A direct wrapper: `modeq.rs`'s
/// `modeq_to_dvd` already builds exactly this proof term as a private step
/// of `mod_eq_dvd_iff`'s own derivation, but never exposed it as its own
/// declared theorem.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_eq_dvd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_dvd, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let modeq_ab = imodeq(d, n, a, b);
        let sub_ba = d.isub(b, a);
        let concl = super::dvd::idvd(d, n, sub_ba);
        let stmt = d.arrow(modeq_ab, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let result = modeq_to_dvd(d, n, a, b, h);
        let proof = d.lam_fv(h_fv, modeq_ab, result);
        (stmt, proof)
    })?;
    Ok(())
}

/// `mod_eq_emod_eq : ∀ n a b, ModEq n a b → Eq Int (emod a n) (emod b n)` --
/// Mathlib's `Int.ModEq.eq`, UNCONDITIONAL in `n`.
///
/// `Int.ModEq n a b` **is defined** as `Eq Int (emod a n) (emod b n)`
/// (`modeq.rs`'s `declare_modeq_definition`): the hypothesis already has
/// exactly the goal's type up to unfolding that one `Definition`, so the
/// proof is the hypothesis itself.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_eq_emod_eq(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_emod_eq, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let modeq_ab = imodeq(d, n, a, b);
        let emod_an = d.iemod(a, n);
        let emod_bn = d.iemod(b, n);
        let concl = d.ieq(emod_an, emod_bn);
        let stmt = d.arrow(modeq_ab, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let proof = d.lam_fv(h_fv, modeq_ab, h);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.ModEq.mul`, UNCONDITIONAL in `n`.
//
// `modeq.rs`'s existing `mod_eq_mul_left`/`mod_eq_mul_right`/`mod_eq_mul` are
// scoped to `0 < n` because they route through `mod_eq_iff_dvd`, which needs
// that bound. Exactly like `declare_modeq_add_right`/`add_left` did for the
// additive family, swapping that bridge for the already-unconditional
// `modeq_to_dvd`/`dvd_to_modeq` removes the hypothesis entirely -- the
// multiplicative case needs one extra step (`mul_sub` to turn
// `dvd n (c*(b-a))` into `dvd n (c*b - c*a)`) that the additive case does not,
// since `Int.add`/`Int.sub` commute with the witness for free while
// `Int.mul`'s distributivity needs a named lemma.
// ---------------------------------------------------------------------------

/// `ModEq n a b → ModEq n (c*a) (c*b)`, UNCONDITIONAL in `n`. Not itself
/// declared as a kernel theorem (no ledger row needs it standalone) --
/// consumed directly by [`declare_mod_eq_mul_general`], mirroring
/// `modeq.rs`'s `modeq_to_dvd`/`dvd_to_modeq` (also un-declared private
/// bridge steps).
fn mod_eq_mul_left_general_term(
    d: &mut IntDev<'_>,
    n: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let dvd_h = modeq_to_dvd(d, n, a, b, h); // dvd n (b-a)
    let sub_ba = d.isub(b, a);
    let c_sub_ba = d.imul(c, sub_ba);
    let mul_left_step = d.const_app(p.dvd_mul_left, &[sub_ba, c]); // dvd sub_ba (c*sub_ba)
    let step1 = d.const_app(p.dvd_trans, &[n, sub_ba, c_sub_ba, dvd_h, mul_left_step]); // dvd n (c*sub_ba)

    let eq_ms = d.const_app(p.mul_sub, &[c, b, a]); // Eq(c*(b-a), c*b - c*a)
    let cb = d.imul(c, b);
    let ca = d.imul(c, a);
    let diff_cb_ca = d.isub(cb, ca);
    let motive = |d: &mut IntDev<'_>, x: ExprId| super::dvd::idvd(d, n, x);
    let dvd_new = d.int_eq_rewrite(c_sub_ba, diff_cb_ca, eq_ms, step1, &motive); // dvd n (c*b - c*a)

    dvd_to_modeq(d, n, ca, cb, dvd_new) // ModEq n (c*a) (c*b)
}

/// `ModEq n a b → ModEq n (a*c) (b*c)`, UNCONDITIONAL in `n`. Commutes
/// [`mod_eq_mul_left_general_term`]'s result via `Int.mul_comm`, exactly as
/// `modeq.rs`'s (conditional) `declare_modeq_mul_right` commutes its own
/// `mul_left` result.
fn mod_eq_mul_right_general_term(
    d: &mut IntDev<'_>,
    n: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let left = mod_eq_mul_left_general_term(d, n, a, b, c, h); // ModEq n (c*a) (c*b)
    let ca = d.imul(c, a);
    let cb = d.imul(c, b);
    let ac = d.imul(a, c);
    let bc = d.imul(b, c);
    let eq1 = d.const_app(p.mul_comm, &[c, a]); // Eq(ca, ac)
    let step1 = d.int_eq_rewrite(ca, ac, eq1, left, &|d, x| imodeq(d, n, x, cb));
    let eq2 = d.const_app(p.mul_comm, &[c, b]); // Eq(cb, bc)
    d.int_eq_rewrite(cb, bc, eq2, step1, &|d, x| imodeq(d, n, ac, x))
}

/// `mod_eq_mul_general : ∀ n a b c e, ModEq n a b → ModEq n c e →
/// ModEq n (a*c) (b*e)` -- Mathlib's `Int.ModEq.mul`, UNCONDITIONAL in `n`
/// (the existing `p.mod_eq_mul` needs `0 < n`; see this section's module-level
/// doc for why).
///
/// Scale the first hypothesis on the right by `c`
/// ([`mod_eq_mul_right_general_term`]), scale the second on the left by `b`
/// ([`mod_eq_mul_left_general_term`]), and chain through `ModEq.trans` --
/// the same composition `modeq.rs`'s conditional `declare_modeq_mul` already
/// uses.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_eq_mul_general(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_mul_general, 5, &|d, v| {
        let (n, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let modeq_ab = imodeq(d, n, a, b);
        let modeq_ce = imodeq(d, n, c, e);
        let ac = d.imul(a, c);
        let be = d.imul(b, e);
        let concl = imodeq(d, n, ac, be);
        let inner_arrow = d.arrow(modeq_ce, concl);
        let stmt = d.arrow(modeq_ab, inner_arrow);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let step1 = mod_eq_mul_right_general_term(d, n, a, b, c, h1); // ModEq n (a*c)(b*c)
        let step2 = mod_eq_mul_left_general_term(d, n, c, e, b, h2); // ModEq n (b*c)(b*e)
        let bc = d.imul(b, c);
        let result = d.const_app(p.mod_eq_trans, &[n, ac, bc, be, step1, step2]);

        let with_h2 = d.lam_fv(h2_fv, modeq_ce, result);
        let proof = d.lam_fv(h1_fv, modeq_ab, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare every theorem this module builds, in dependency order (none of
/// them depend on each other except [`declare_mod_eq_add_right_cancel_single`]
/// being needed by [`declare_mod_eq_add_right_cancel_general`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection if any constructed term does not
/// check.
pub(super) fn declare_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_dvd_gcd_nat(d)?;
    declare_dvd_gcd_nat_iff(d)?;
    declare_dvd_coe_gcd_iff(d)?;
    declare_ediv_gcd_ne_zero_of_ne_zero_left(d)?;
    declare_ediv_gcd_ne_zero_if_ne_zero_right(d)?;
    declare_mod_eq_add(d)?;
    declare_mod_eq_add_right_cancel_single(d)?;
    declare_mod_eq_add_left_cancel_general(d)?;
    declare_mod_eq_add_right_cancel_general(d)?;
    declare_mod_eq_dvd(d)?;
    declare_mod_eq_emod_eq(d)?;
    declare_mod_eq_mul_general(d)?;
    Ok(())
}
