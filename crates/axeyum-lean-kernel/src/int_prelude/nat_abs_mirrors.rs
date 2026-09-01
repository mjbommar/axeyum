//! Mathlib's `Int.natAbs` order and injectivity mirrors.
//!
//! Landed as the scored attempt at the held-out `integer-absolute-value`
//! family (see
//! `docs/research/11-design-review/2026-09-01-scoring-protocol-preregistration.md`).
//!
//! Everything here rests on one structural fact about this construction, and
//! the whole family is cheap *because* of it: `Int.le` and `Int.lt` are
//! **four-case computing definitions** over `Nat.le`/`Nat.lt`
//! ([`super::defs`]), and `Int.natAbs` computes on both constructors. So after
//! an `Int.rec` split of the quantified variables, every goal in this file has
//! already ι-reduced to a statement about naturals, to `True`, or to `False`.
//!
//! In particular a sign hypothesis is *self-discharging* in the branches it
//! excludes: `Int.le Int.zero (Int.negSucc n)` **is** `False`, so those
//! branches close by `absurd` on the hypothesis itself with no arithmetic. The
//! four `natAbs_inj_of_*` mirrors each keep only one or two live branches out
//! of four for exactly this reason.
//!
//! The recurring move in the live branches is the pair in
//! [`IntDev::int_eq_rewrite`]'s own doc comment:
//!
//! * **injectivity** — from `h : Eq Int (ofNat m) (ofNat n)`, transport
//!   `Eq Nat (natAbs (ofNat m)) (natAbs y)` along `h`. Because `natAbs` computes
//!   on `ofNat`, the `refl` case is `Eq Nat m m` and the result is `Eq Nat m n`.
//!   No `Int.ofNat.inj` lemma is needed, and none exists here.
//! * **discrimination** — from `h : Eq Int (ofNat m) (negSucc n)`, transport
//!   `Int.le Int.zero y` along `h`. The `refl` case is `Nat.le 0 m`
//!   (`Nat.zero_le`) and the result reduces to `False`.
//!
//! `Int.zero` is a `Definition` whose value is `Int.ofNat Nat.zero`, so it
//! delta-unfolds into the four-case split and both moves fire on it.

use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::{Branch, IntDev, Shape, case_split};

/// `Int.natAbs a`, as a term.
trait NatAbsOps {
    fn nat_abs(&mut self, a: ExprId) -> ExprId;
}

impl NatAbsOps for IntDev<'_> {
    fn nat_abs(&mut self, a: ExprId) -> ExprId {
        let name = self.int().nat_abs;
        self.const_app(name, &[a])
    }
}

/// `Iff p q`, as a term.
fn iff(d: &mut IntDev<'_>, p: ExprId, q: ExprId) -> ExprId {
    let name = d.int().logic.iff;
    d.const_app(name, &[p, q])
}

/// `Iff.intro p q mp mpr : Iff p q`.
fn iff_intro(d: &mut IntDev<'_>, p: ExprId, q: ExprId, mp: ExprId, mpr: ExprId) -> ExprId {
    let name = d.int().logic.iff_intro;
    d.const_app(name, &[p, q, mp, mpr])
}

/// `Nat.zero_le n : Nat.le 0 n`.
fn nat_zero_le(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let name = d.int().nat.zero_le;
    d.const_app(name, &[n])
}

/// From `h : Eq Int p q` where `p` is non-negative-shaped and `q` is
/// `negSucc`-shaped, produce a proof of `target` by discrimination.
///
/// The transported proposition is `Int.le Int.zero y`. At `y := p` it reduces to
/// `Nat.le 0 (natAbs p)` and is discharged by `Nat.zero_le`; at `y := q` it
/// reduces to `False`. `nonneg_witness` is that `Nat.zero_le`, stated at
/// whatever natural `p`'s reduct exposes.
fn discriminate_by_sign(
    d: &mut IntDev<'_>,
    p: ExprId,
    q: ExprId,
    h: ExprId,
    nonneg_witness: ExprId,
    target: ExprId,
) -> ExprId {
    let contradiction = d.int_eq_rewrite(p, q, h, nonneg_witness, &|d, y| {
        let zero = d.izero();
        d.ile(zero, y)
    });
    d.absurd(target, contradiction)
}

/// `Iff (Eq Nat (natAbs (ofNat m)) (natAbs (ofNat n))) (Eq Int (ofNat m) (ofNat n))`.
///
/// The workhorse of this module: after any split that leaves both sides
/// `ofNat`-shaped, every `natAbs_inj_of_*` branch is exactly this.
fn of_nat_inj_iff(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> (ExprId, ExprId) {
    let left = {
        let lhs = d.of_nat(m);
        let rhs = d.of_nat(n);
        let a = d.nat_abs(lhs);
        let b = d.nat_abs(rhs);
        d.eq(a, b)
    };
    let right = {
        let lhs = d.of_nat(m);
        let rhs = d.of_nat(n);
        d.ieq(lhs, rhs)
    };
    // Forward: `m = n` pushed through `Int.ofNat`.
    let mp = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.nat_eq_to_int(m, n, h, &|d, x| d.of_nat(x));
        d.lam_fv(h_fv, left, body)
    };
    // Backward: transport `Eq Nat (natAbs (ofNat m)) (natAbs y)` along the
    // integer equation. `natAbs (ofNat _)` computes, so the refl case is
    // `Eq Nat m m`.
    let mpr = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let lhs = d.of_nat(m);
        let rhs = d.of_nat(n);
        let refl_case = d.refl(m);
        let body = d.int_eq_rewrite(lhs, rhs, h, refl_case, &|d, y| {
            let l = d.of_nat(m);
            let a = d.nat_abs(l);
            let b = d.nat_abs(y);
            d.eq(a, b)
        });
        d.lam_fv(h_fv, right, body)
    };
    let proof = iff_intro(d, left, right, mp, mpr);
    (iff(d, left, right), proof)
}

/// `Iff (Eq Nat (natAbs (negSucc m)) (natAbs (negSucc n))) (Eq Int (negSucc m) (negSucc n))`.
fn neg_succ_inj_iff(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let left = {
        let lhs = d.neg_succ(m);
        let rhs = d.neg_succ(n);
        let a = d.nat_abs(lhs);
        let b = d.nat_abs(rhs);
        d.eq(a, b)
    };
    let right = {
        let lhs = d.neg_succ(m);
        let rhs = d.neg_succ(n);
        d.ieq(lhs, rhs)
    };
    // Forward: `succ m = succ n` gives `m = n` by `Nat.succ_injective`, then
    // push through `Int.negSucc`.
    let mp = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let inj = d.int().nat.succ_injective;
        let inner = d.const_app(inj, &[m, n, h]);
        let body = d.nat_eq_to_int(m, n, inner, &|d, x| d.neg_succ(x));
        d.lam_fv(h_fv, left, body)
    };
    let mpr = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let lhs = d.neg_succ(m);
        let rhs = d.neg_succ(n);
        let magnitude = d.succ(m);
        let refl_case = d.refl(magnitude);
        let body = d.int_eq_rewrite(lhs, rhs, h, refl_case, &|d, y| {
            let l = d.neg_succ(m);
            let a = d.nat_abs(l);
            let b = d.nat_abs(y);
            d.eq(a, b)
        });
        d.lam_fv(h_fv, right, body)
    };
    iff_intro(d, left, right, mp, mpr)
}

/// `nat_abs_inj_of_nonneg_of_nonneg : 0 ≤ a → 0 ≤ b → (natAbs a = natAbs b ↔ a = b)`.
///
/// Mirrors Mathlib's `Int.natAbs_inj_of_nonneg_of_nonneg`
/// (`Mathlib/Data/Int/Lemmas.lean:51`).
///
/// Three of the four branches are closed by the sign hypotheses alone: any
/// `negSucc` in a non-negative position makes `Int.le Int.zero _` reduce to
/// `False`. Only `(ofNat, ofNat)` survives, and it is [`of_nat_inj_iff`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_inj_of_nonneg_of_nonneg(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_inj_of_nonneg_of_nonneg, 2, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (a, b) = (args[0], args[1]);
            let zero = d.izero();
            let ha = d.ile(zero, a);
            let hb = d.ile(zero, b);
            let left = {
                let x = d.nat_abs(a);
                let y = d.nat_abs(b);
                d.eq(x, y)
            };
            let right = d.ieq(a, b);
            let concl = iff(d, left, right);
            let inner = d.arrow(hb, concl);
            d.arrow(ha, inner)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, b: &[Branch]| {
            let (sa, ma) = b[0];
            let (sb, mb) = b[1];
            let a_term = d.branch_term(b[0]);
            let b_term = d.branch_term(b[1]);
            let zero = d.izero();
            let ha_ty = d.ile(zero, a_term);
            let hb_ty = d.ile(zero, b_term);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let goal = {
                let left = {
                    let x = d.nat_abs(a_term);
                    let y = d.nat_abs(b_term);
                    d.eq(x, y)
                };
                let right = d.ieq(a_term, b_term);
                iff(d, left, right)
            };
            let body = match (sa, sb) {
                (Shape::OfNat, Shape::OfNat) => of_nat_inj_iff(d, ma, mb).1,
                // `0 <= negSucc _` IS `False`; whichever hypothesis lands on a
                // `negSucc` closes the branch.
                (Shape::NegSucc, _) => d.absurd(goal, ha),
                (Shape::OfNat, Shape::NegSucc) => d.absurd(goal, hb),
            };
            let inner = d.lam_fv(hb_fv, hb_ty, body);
            d.lam_fv(ha_fv, ha_ty, inner)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `nat_abs_inj_of_nonpos_of_nonpos : a ≤ 0 → b ≤ 0 → (natAbs a = natAbs b ↔ a = b)`.
///
/// Mirrors Mathlib's `Int.natAbs_inj_of_nonpos_of_nonpos`
/// (`Mathlib/Data/Int/Lemmas.lean:54`).
///
/// Unlike the non-negative case, `negSucc _ ≤ 0` reduces to `True`, so no
/// branch is excluded by a hypothesis. All four are live, and the two
/// **mixed-sign** ones are where the work is: the sign hypothesis on the
/// `ofNat` side reduces to `Nat.le m 0`, and the branch is closed by observing
/// that both sides of the `Iff` are false — `Nat.succ _ = 0` by
/// `Nat.not_succ_le_zero` after rewriting, and the integer equation by
/// discrimination.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_inj_of_nonpos_of_nonpos(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_inj_of_nonpos_of_nonpos, 2, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (a, b) = (args[0], args[1]);
            let zero = d.izero();
            let ha = d.ile(a, zero);
            let hb = d.ile(b, zero);
            let left = {
                let x = d.nat_abs(a);
                let y = d.nat_abs(b);
                d.eq(x, y)
            };
            let right = d.ieq(a, b);
            let concl = iff(d, left, right);
            let inner = d.arrow(hb, concl);
            d.arrow(ha, inner)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, br: &[Branch]| {
            let (sa, ma) = br[0];
            let (sb, mb) = br[1];
            let a_term = d.branch_term(br[0]);
            let b_term = d.branch_term(br[1]);
            let zero = d.izero();
            let ha_ty = d.ile(a_term, zero);
            let hb_ty = d.ile(b_term, zero);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let left = {
                let x = d.nat_abs(a_term);
                let y = d.nat_abs(b_term);
                d.eq(x, y)
            };
            let right = d.ieq(a_term, b_term);
            // All four branches are live here (`negSucc _ <= 0` is `True`), so
            // unlike the other three mirrors there is no `absurd` case and the
            // whole `Iff` is never needed as a single term.
            let body = match (sa, sb) {
                (Shape::OfNat, Shape::OfNat) => of_nat_inj_iff(d, ma, mb).1,
                (Shape::NegSucc, Shape::NegSucc) => neg_succ_inj_iff(d, ma, mb),
                // `ofNat m ≤ 0` is `Nat.le m 0`; the magnitude equation says
                // `m = succ n`, and rewriting the bound along it gives
                // `Nat.le (succ n) 0`, refuted outright.
                (Shape::OfNat, Shape::NegSucc) => {
                    let mp = {
                        let h_fv = d.fresh_fvar();
                        let h = d.kernel().fvar(h_fv);
                        let succ_n = d.succ(mb);
                        let moved = d.nat_rewrite(ma, succ_n, h, ha, &|d, x| {
                            let z = d.zero();
                            d.le(x, z)
                        });
                        let refute = d.int().nat.not_succ_le_zero;
                        let contradiction = d.const_app(refute, &[mb, moved]);
                        let body = d.absurd(right, contradiction);
                        d.lam_fv(h_fv, left, body)
                    };
                    let mpr = {
                        let h_fv = d.fresh_fvar();
                        let h = d.kernel().fvar(h_fv);
                        let witness = nat_zero_le(d, ma);
                        let body = discriminate_by_sign(d, a_term, b_term, h, witness, left);
                        d.lam_fv(h_fv, right, body)
                    };
                    iff_intro(d, left, right, mp, mpr)
                }
                // The mirror image; the `Nat.le _ 0` bound now sits on `b`.
                (Shape::NegSucc, Shape::OfNat) => {
                    let mp = {
                        let h_fv = d.fresh_fvar();
                        let h = d.kernel().fvar(h_fv);
                        let succ_m = d.succ(ma);
                        // `h : succ m = n`; move the bound `Nat.le n 0` back
                        // onto `succ m`.
                        let back = d.symm(succ_m, mb, h);
                        let moved = d.nat_rewrite(mb, succ_m, back, hb, &|d, x| {
                            let z = d.zero();
                            d.le(x, z)
                        });
                        let refute = d.int().nat.not_succ_le_zero;
                        let contradiction = d.const_app(refute, &[ma, moved]);
                        let body = d.absurd(right, contradiction);
                        d.lam_fv(h_fv, left, body)
                    };
                    let mpr = {
                        let h_fv = d.fresh_fvar();
                        let h = d.kernel().fvar(h_fv);
                        // `h : negSucc m = ofNat n`; flip it and discriminate.
                        let back = d.isymm(a_term, b_term, h);
                        let witness = nat_zero_le(d, mb);
                        let body = discriminate_by_sign(d, b_term, a_term, back, witness, left);
                        d.lam_fv(h_fv, right, body)
                    };
                    iff_intro(d, left, right, mp, mpr)
                }
            };
            let inner = d.lam_fv(hb_fv, hb_ty, body);
            d.lam_fv(ha_fv, ha_ty, inner)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `nat_abs_inj_of_nonneg_of_nonpos : 0 ≤ a → b ≤ 0 → (natAbs a = natAbs b ↔ a = -b)`.
///
/// Mirrors Mathlib's `Int.natAbs_inj_of_nonneg_of_nonpos`
/// (`Mathlib/Data/Int/Lemmas.lean:59`).
///
/// `a` must be `ofNat`-shaped. The `(ofNat, negSucc)` branch is free:
/// `Int.neg (negSucc n)` **reduces** to `ofNat (succ n)`, so the goal is
/// literally [`of_nat_inj_iff`] at `(m, succ n)`.
///
/// The `(ofNat, ofNat)` branch is the one that costs something, and for a
/// reason worth recording: `Int.neg (ofNat n)` is `Int.negOfNat n`, a case
/// analysis on `n` that is **stuck for a symbolic `n`**. It is unstuck by
/// `n = 0`, which the hypothesis `Nat.le n 0` gives through
/// `Nat.le_antisymm`; the whole `Iff` is then transported back along that
/// equation.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_inj_of_nonneg_of_nonpos(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_inj_of_nonneg_of_nonpos, 2, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (a, b) = (args[0], args[1]);
            let zero = d.izero();
            let ha = d.ile(zero, a);
            let hb = d.ile(b, zero);
            let left = {
                let x = d.nat_abs(a);
                let y = d.nat_abs(b);
                d.eq(x, y)
            };
            let right = {
                let negated = d.ineg(b);
                d.ieq(a, negated)
            };
            let concl = iff(d, left, right);
            let inner = d.arrow(hb, concl);
            d.arrow(ha, inner)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, br: &[Branch]| {
            let (sa, ma) = br[0];
            let (sb, mb) = br[1];
            let a_term = d.branch_term(br[0]);
            let b_term = d.branch_term(br[1]);
            let zero = d.izero();
            let ha_ty = d.ile(zero, a_term);
            let hb_ty = d.ile(b_term, zero);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let goal = {
                let left = {
                    let x = d.nat_abs(a_term);
                    let y = d.nat_abs(b_term);
                    d.eq(x, y)
                };
                let right = {
                    let negated = d.ineg(b_term);
                    d.ieq(a_term, negated)
                };
                iff(d, left, right)
            };
            let body = match (sa, sb) {
                // `0 <= negSucc m` is `False`.
                (Shape::NegSucc, _) => d.absurd(goal, ha),
                // `neg (negSucc n)` reduces to `ofNat (succ n)`, and
                // `natAbs (negSucc n)` reduces to `succ n`, so this branch IS
                // `of_nat_inj_iff` at `(m, succ n)` up to iota.
                (Shape::OfNat, Shape::NegSucc) => {
                    let succ_n = d.succ(mb);
                    of_nat_inj_iff(d, ma, succ_n).1
                }
                // `neg (ofNat n)` is `negOfNat n`, stuck for symbolic `n`.
                // `Nat.le n 0` plus `Nat.zero_le n` gives `n = 0` by
                // antisymmetry, which unsticks it.
                (Shape::OfNat, Shape::OfNat) => {
                    let zero_nat = d.zero();
                    let anti = d.int().nat.le_antisymm;
                    let lower = nat_zero_le(d, mb);
                    // `hb : Nat.le n 0`, `lower : Nat.le 0 n`.
                    let n_is_zero = d.const_app(anti, &[mb, zero_nat, hb, lower]);
                    let back = d.symm(mb, zero_nat, n_is_zero);
                    // Prove the goal with `n := 0`, then transport back.
                    let at_zero = of_nat_inj_iff(d, ma, zero_nat).1;
                    d.nat_rewrite(zero_nat, mb, back, at_zero, &|d, x| {
                        let l = d.of_nat(ma);
                        let r = d.of_nat(x);
                        let left = {
                            let p = d.nat_abs(l);
                            let q = d.nat_abs(r);
                            d.eq(p, q)
                        };
                        let right = {
                            let negated = d.ineg(r);
                            d.ieq(l, negated)
                        };
                        iff(d, left, right)
                    })
                }
            };
            let inner = d.lam_fv(hb_fv, hb_ty, body);
            d.lam_fv(ha_fv, ha_ty, inner)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `nat_abs_inj_of_nonpos_of_nonneg : a ≤ 0 → 0 ≤ b → (natAbs a = natAbs b ↔ -a = b)`.
///
/// Mirrors Mathlib's `Int.natAbs_inj_of_nonpos_of_nonneg`
/// (`Mathlib/Data/Int/Lemmas.lean:63`). The mirror image of
/// [`declare_nat_abs_inj_of_nonneg_of_nonpos`], with the stuck `negOfNat` now
/// on the left of the integer equation.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_inj_of_nonpos_of_nonneg(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_inj_of_nonpos_of_nonneg, 2, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (a, b) = (args[0], args[1]);
            let zero = d.izero();
            let ha = d.ile(a, zero);
            let hb = d.ile(zero, b);
            let left = {
                let x = d.nat_abs(a);
                let y = d.nat_abs(b);
                d.eq(x, y)
            };
            let right = {
                let negated = d.ineg(a);
                d.ieq(negated, b)
            };
            let concl = iff(d, left, right);
            let inner = d.arrow(hb, concl);
            d.arrow(ha, inner)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, br: &[Branch]| {
            let (sa, ma) = br[0];
            let (sb, mb) = br[1];
            let a_term = d.branch_term(br[0]);
            let b_term = d.branch_term(br[1]);
            let zero = d.izero();
            let ha_ty = d.ile(a_term, zero);
            let hb_ty = d.ile(zero, b_term);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let goal = {
                let left = {
                    let x = d.nat_abs(a_term);
                    let y = d.nat_abs(b_term);
                    d.eq(x, y)
                };
                let right = {
                    let negated = d.ineg(a_term);
                    d.ieq(negated, b_term)
                };
                iff(d, left, right)
            };
            let body = match (sa, sb) {
                // `0 <= negSucc n` is `False`.
                (_, Shape::NegSucc) => d.absurd(goal, hb),
                // `neg (negSucc m)` reduces to `ofNat (succ m)`.
                (Shape::NegSucc, Shape::OfNat) => {
                    let succ_m = d.succ(ma);
                    of_nat_inj_iff(d, succ_m, mb).1
                }
                // `neg (ofNat m)` is stuck; `Nat.le m 0` gives `m = 0`.
                (Shape::OfNat, Shape::OfNat) => {
                    let zero_nat = d.zero();
                    let anti = d.int().nat.le_antisymm;
                    let lower = nat_zero_le(d, ma);
                    let m_is_zero = d.const_app(anti, &[ma, zero_nat, ha, lower]);
                    let back = d.symm(ma, zero_nat, m_is_zero);
                    let at_zero = of_nat_inj_iff(d, zero_nat, mb).1;
                    d.nat_rewrite(zero_nat, ma, back, at_zero, &|d, x| {
                        let l = d.of_nat(x);
                        let r = d.of_nat(mb);
                        let left = {
                            let p = d.nat_abs(l);
                            let q = d.nat_abs(r);
                            d.eq(p, q)
                        };
                        let right = {
                            let negated = d.ineg(l);
                            d.ieq(negated, r)
                        };
                        iff(d, left, right)
                    })
                }
            };
            let inner = d.lam_fv(hb_fv, hb_ty, body);
            d.lam_fv(ha_fv, ha_ty, inner)
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The `mul_self` cluster
// ---------------------------------------------------------------------------
//
// `Int.mul` is a four-case computing definition too (`super::defs`), and both
// same-sign cases land on `ofNat`:
//
//     mul (ofNat m)   (ofNat n)   ≡ ofNat (m * n)
//     mul (negSucc m) (negSucc n) ≡ ofNat (succ m * succ n)
//
// So `a * a` is `ofNat (natAbs a * natAbs a)` on **both** constructors, and
// `Int.le` then reduces the comparison to `Nat.le`. Every one of the four
// branches of `natAbs_le_iff_mul_self_le` and its siblings therefore collapses
// to the same `Nat` statement at `(natAbs a, natAbs b)`, and the entire content
// of the three mirrors is the three `Nat` squaring lemmas below.
//
// Mathlib reaches these through `abs_le_iff_mul_self_le` and the
// linear-ordered-ring API; nothing of that kind is needed or used here.

/// `Nat.le_of_lt` — absent from the prelude, and one `le_trans` away.
fn nat_le_of_lt(d: &mut IntDev<'_>, m: ExprId, n: ExprId, h: ExprId) -> ExprId {
    let succ_m = d.succ(m);
    let step = {
        let name = d.int().nat.le_succ;
        d.const_app(name, &[m])
    };
    let trans = d.int().nat.le_trans;
    d.const_app(trans, &[m, succ_m, n, step, h])
}

/// `0 < n` from `h : m < n`, for any `m`.
fn nat_pos_of_lt(d: &mut IntDev<'_>, m: ExprId, n: ExprId, h: ExprId) -> ExprId {
    let zero = d.zero();
    let lower = nat_zero_le(d, m);
    let name = d.int().nat.lt_of_le_of_lt;
    d.const_app(name, &[zero, m, n, lower, h])
}

/// `m * m ≤ n * n` from `h : m ≤ n`.
///
/// `m*m ≤ m*n` by left-multiplying `h`, and `m*n ≤ n*n` by left-multiplying it
/// by `n` and commuting. `Nat.mul_le_mul_right` does not exist here, which is
/// why the commutation is explicit.
fn nat_mul_self_le(d: &mut IntDev<'_>, m: ExprId, n: ExprId, h: ExprId) -> ExprId {
    let mul_le = d.int().nat.mul_le_mul_left;
    let mm = NatOps::mul(d, m, m);
    let mn = NatOps::mul(d, m, n);
    let nn = NatOps::mul(d, n, n);
    let first = d.const_app(mul_le, &[m, m, n, h]);
    // `n * m ≤ n * n`, then rewrite `n * m` to `m * n`.
    let nm = NatOps::mul(d, n, m);
    let second_raw = d.const_app(mul_le, &[n, m, n, h]);
    let comm = {
        let name = d.int().nat.mul_comm;
        d.const_app(name, &[n, m])
    };
    let second = d.nat_rewrite(nm, mn, comm, second_raw, &|d, x| {
        let rhs = NatOps::mul(d, n, n);
        d.le(x, rhs)
    });
    let trans = d.int().nat.le_trans;
    d.const_app(trans, &[mm, mn, nn, first, second])
}

/// `m * m < n * n` from `h : m < n`.
///
/// `m*m ≤ m*n` (weakening `h`), then `m*n < n*n` by `Nat.mul_lt_mul_right` at
/// the positive multiplier `n`, whose positivity comes from `h` itself.
fn nat_mul_self_lt(d: &mut IntDev<'_>, m: ExprId, n: ExprId, h: ExprId) -> ExprId {
    let mul_le = d.int().nat.mul_le_mul_left;
    let weak = nat_le_of_lt(d, m, n, h);
    let mm = NatOps::mul(d, m, m);
    let mn = NatOps::mul(d, m, n);
    let nn = NatOps::mul(d, n, n);
    let first = d.const_app(mul_le, &[m, m, n, weak]);
    let positive = nat_pos_of_lt(d, m, n, h);
    let strict = {
        let name = d.int().nat.mul_lt_mul_right;
        let equiv = d.const_app(name, &[n, m, n, positive]);
        let lhs = d.lt(mn, nn);
        let rhs = d.lt(m, n);
        let mpr = d.int().logic.iff_mpr;
        d.const_app(mpr, &[lhs, rhs, equiv, h])
    };
    let name = d.int().nat.lt_of_le_of_lt;
    d.const_app(name, &[mm, mn, nn, first, strict])
}

/// `Nat.mul_self_le_mul_self_iff : ∀ m n, m ≤ n ↔ m * m ≤ n * n`.
///
/// Declared into the `Nat` namespace from the `Int` prelude, the way
/// `wilson.rs` declares `Nat.inverseIndex`: the statement is pure `Nat` and
/// belongs there, but its only consumers so far are the `Int.natAbs` mirrors
/// below. Verified absent from the whole constructed inventory before naming
/// (positive control: `Nat.mul_le_mul_left`, 8 rows).
///
/// The reverse direction is where the content is, and it is a refutation:
/// `Nat.lt_or_ge` splits on `n < m`, which gives `n*n < m*m` and so contradicts
/// `m*m ≤ n*n` outright.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_mul_self_le_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.nat_mul_self_le_mul_self_iff, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let left = d.le(m, n);
        let right = {
            let mm = NatOps::mul(d, m, m);
            let nn = NatOps::mul(d, n, n);
            d.le(mm, nn)
        };
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = nat_mul_self_le(d, m, n, h);
            d.lam_fv(h_fv, left, body)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let split = {
                let name = d.int().nat.lt_or_ge;
                d.const_app(name, &[n, m])
            };
            let lt_case = d.lt(n, m);
            let ge_case = d.le(m, n);
            let body = d.or_elim(
                lt_case,
                ge_case,
                left,
                split,
                &|d, hlt| {
                    // `n < m` gives `n*n < m*m`, which with `m*m ≤ n*n`
                    // yields `n*n < n*n`.
                    let strict = nat_mul_self_lt(d, n, m, hlt);
                    let nn = NatOps::mul(d, n, n);
                    let mm = NatOps::mul(d, m, m);
                    let chained = {
                        let name = d.int().nat.lt_of_lt_of_le;
                        d.const_app(name, &[nn, mm, nn, strict, h])
                    };
                    let irrefl = d.int().nat.lt_irrefl;
                    let contradiction = d.const_app(irrefl, &[nn, chained]);
                    let target = d.le(m, n);
                    d.absurd(target, contradiction)
                },
                &|_d, hge| hge,
            );
            d.lam_fv(h_fv, right, body)
        };
        let stmt = iff(d, left, right);
        let proof = iff_intro(d, left, right, mp, mpr);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.mul_self_lt_mul_self_iff : ∀ m n, m < n ↔ m * m < n * n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_mul_self_lt_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.nat_mul_self_lt_mul_self_iff, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let left = d.lt(m, n);
        let right = {
            let mm = NatOps::mul(d, m, m);
            let nn = NatOps::mul(d, n, n);
            d.lt(mm, nn)
        };
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = nat_mul_self_lt(d, m, n, h);
            d.lam_fv(h_fv, left, body)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let split = {
                let name = d.int().nat.lt_or_ge;
                d.const_app(name, &[m, n])
            };
            let lt_case = d.lt(m, n);
            let ge_case = d.le(n, m);
            let body = d.or_elim(lt_case, ge_case, left, split, &|_d, hlt| hlt, &|d, hge| {
                // `n ≤ m` gives `n*n ≤ m*m`, contradicting `m*m < n*n`.
                let weak = nat_mul_self_le(d, n, m, hge);
                let mm = NatOps::mul(d, m, m);
                let nn = NatOps::mul(d, n, n);
                let chained = {
                    let name = d.int().nat.lt_of_lt_of_le;
                    d.const_app(name, &[mm, nn, mm, h, weak])
                };
                let irrefl = d.int().nat.lt_irrefl;
                let contradiction = d.const_app(irrefl, &[mm, chained]);
                let target = d.lt(m, n);
                d.absurd(target, contradiction)
            });
            d.lam_fv(h_fv, right, body)
        };
        let stmt = iff(d, left, right);
        let proof = iff_intro(d, left, right, mp, mpr);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.mul_self_eq_mul_self_iff : ∀ m n, m = n ↔ m * m = n * n`.
///
/// The reverse direction is antisymmetry applied to
/// [`declare_mul_self_le_iff`] in both directions: an equation gives both
/// `m*m ≤ n*n` and `n*n ≤ m*m` by transporting `Nat.le_refl`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_mul_self_eq_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.nat_mul_self_eq_mul_self_iff, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let left = d.eq(m, n);
        let right = {
            let mm = NatOps::mul(d, m, m);
            let nn = NatOps::mul(d, n, n);
            d.eq(mm, nn)
        };
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.congr(m, n, h, &|d, x| NatOps::mul(d, x, x));
            d.lam_fv(h_fv, left, body)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let mm = NatOps::mul(d, m, m);
            let nn = NatOps::mul(d, n, n);
            let refl_mm = {
                let name = d.int().nat.le_refl;
                d.const_app(name, &[mm])
            };
            // `m*m ≤ n*n` by moving `Nat.le_refl (m*m)` along `h`.
            let forward = d.nat_rewrite(mm, nn, h, refl_mm, &|d, x| {
                let l = NatOps::mul(d, m, m);
                d.le(l, x)
            });
            // `n*n ≤ m*m` by moving it the other way.
            let back = d.symm(mm, nn, h);
            let refl_nn = {
                let name = d.int().nat.le_refl;
                d.const_app(name, &[nn])
            };
            let backward = d.nat_rewrite(nn, mm, back, refl_nn, &|d, x| {
                let l = NatOps::mul(d, n, n);
                d.le(l, x)
            });
            let iff_name = p.nat_mul_self_le_mul_self_iff;
            let mpr_name = d.int().logic.iff_mpr;
            let m_le_n = {
                let equiv = d.const_app(iff_name, &[m, n]);
                let l = d.le(m, n);
                let r = {
                    let a = NatOps::mul(d, m, m);
                    let b = NatOps::mul(d, n, n);
                    d.le(a, b)
                };
                d.const_app(mpr_name, &[l, r, equiv, forward])
            };
            let n_le_m = {
                let equiv = d.const_app(iff_name, &[n, m]);
                let l = d.le(n, m);
                let r = {
                    let a = NatOps::mul(d, n, n);
                    let b = NatOps::mul(d, m, m);
                    d.le(a, b)
                };
                d.const_app(mpr_name, &[l, r, equiv, backward])
            };
            let anti = d.int().nat.le_antisymm;
            let body = d.const_app(anti, &[m, n, m_le_n, n_le_m]);
            d.lam_fv(h_fv, right, body)
        };
        let stmt = iff(d, left, right);
        let proof = iff_intro(d, left, right, mp, mpr);
        (stmt, proof)
    })?;
    Ok(())
}

/// The magnitude a branch's constructor exposes: `natAbs (ofNat k) ≡ k` and
/// `natAbs (negSucc k) ≡ succ k`.
fn branch_magnitude(d: &mut IntDev<'_>, b: Branch) -> ExprId {
    match b.0 {
        Shape::OfNat => b.1,
        Shape::NegSucc => d.succ(b.1),
    }
}

/// `nat_abs_le_iff_mul_self_le : natAbs a ≤ natAbs b ↔ a * a ≤ b * b`.
///
/// Mirrors Mathlib's `Int.natAbs_le_iff_mul_self_le`
/// (`Mathlib/Data/Int/Order/Lemmas.lean:34`). Every branch has already reduced
/// to `Nat.mul_self_le_mul_self_iff` at the two magnitudes.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_le_iff_mul_self_le(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_le_iff_mul_self_le, 2, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (a, b) = (args[0], args[1]);
            let left = {
                let x = d.nat_abs(a);
                let y = d.nat_abs(b);
                d.le(x, y)
            };
            let right = {
                let aa = d.imul(a, a);
                let bb = d.imul(b, b);
                d.ile(aa, bb)
            };
            iff(d, left, right)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, br: &[Branch]| {
            let x = branch_magnitude(d, br[0]);
            let y = branch_magnitude(d, br[1]);
            d.const_app(p.nat_mul_self_le_mul_self_iff, &[x, y])
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `nat_abs_lt_iff_mul_self_lt : natAbs a < natAbs b ↔ a * a < b * b`.
///
/// Mirrors Mathlib's `Int.natAbs_lt_iff_mul_self_lt`
/// (`Mathlib/Data/Int/Order/Lemmas.lean:30`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_lt_iff_mul_self_lt(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_lt_iff_mul_self_lt, 2, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (a, b) = (args[0], args[1]);
            let left = {
                let x = d.nat_abs(a);
                let y = d.nat_abs(b);
                d.lt(x, y)
            };
            let right = {
                let aa = d.imul(a, a);
                let bb = d.imul(b, b);
                d.ilt(aa, bb)
            };
            iff(d, left, right)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, br: &[Branch]| {
            let x = branch_magnitude(d, br[0]);
            let y = branch_magnitude(d, br[1]);
            d.const_app(p.nat_mul_self_lt_mul_self_iff, &[x, y])
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `nat_abs_eq_iff_mul_self_eq : natAbs a = natAbs b ↔ a * a = b * b`.
///
/// Mirrors Mathlib's `Int.natAbs_eq_iff_mul_self_eq`
/// (`Mathlib/Data/Int/Order/Lemmas.lean:26`).
///
/// The one shape that is **not** free: the right-hand side is an equation
/// between integers, and `Int.ofNat` is a constructor rather than a computing
/// head, so the reduced goal is `Eq Int (ofNat (x*x)) (ofNat (y*y))` and not an
/// equation between naturals. It is bridged by the same injectivity /
/// congruence pair [`of_nat_inj_iff`] uses, wrapped around
/// `Nat.mul_self_eq_mul_self_iff`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_eq_iff_mul_self_eq(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.nat_abs_eq_iff_mul_self_eq, 2, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (a, b) = (args[0], args[1]);
            let left = {
                let x = d.nat_abs(a);
                let y = d.nat_abs(b);
                d.eq(x, y)
            };
            let right = {
                let aa = d.imul(a, a);
                let bb = d.imul(b, b);
                d.ieq(aa, bb)
            };
            iff(d, left, right)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, br: &[Branch]| {
            let x = branch_magnitude(d, br[0]);
            let y = branch_magnitude(d, br[1]);
            let xx = NatOps::mul(d, x, x);
            let yy = NatOps::mul(d, y, y);
            let nat_left = d.eq(x, y);
            let nat_right = d.eq(xx, yy);
            let squares = d.const_app(p.nat_mul_self_eq_mul_self_iff, &[x, y]);
            let mp_name = d.int().logic.iff_mp;
            let mpr_name = d.int().logic.iff_mpr;
            let int_right = {
                let l = d.of_nat(xx);
                let r = d.of_nat(yy);
                d.ieq(l, r)
            };
            // Forward: the magnitude equation gives `x*x = y*y`, pushed
            // through `Int.ofNat` -- which is what `a*a` and `b*b` reduced to.
            let mp = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let nat_eq = d.const_app(mp_name, &[nat_left, nat_right, squares, h]);
                let body = d.nat_eq_to_int(xx, yy, nat_eq, &|d, z| d.of_nat(z));
                d.lam_fv(h_fv, nat_left, body)
            };
            // Backward: recover `x*x = y*y` by transporting `natAbs` along the
            // integer equation, then invert the squaring lemma.
            let mpr = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let lhs = d.of_nat(xx);
                let rhs = d.of_nat(yy);
                let refl_case = d.refl(xx);
                let nat_eq = d.int_eq_rewrite(lhs, rhs, h, refl_case, &|d, z| {
                    let l = d.of_nat(xx);
                    let a = d.nat_abs(l);
                    let b = d.nat_abs(z);
                    d.eq(a, b)
                });
                let body = d.const_app(mpr_name, &[nat_left, nat_right, squares, nat_eq]);
                d.lam_fv(h_fv, int_right, body)
            };
            iff_intro(d, nat_left, int_right, mp, mpr)
        });
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The `coe_sub_coe` pair
// ---------------------------------------------------------------------------
//
// These two quantify over **naturals**, not integers, so they are `d.theorem`
// rather than `d.int_theorem`, and the case analysis is on the *difference*
// rather than on a variable.
//
// `Int.sub` is a `Definition` unfolding to `add x (neg y)`, and
// `neg (ofNat b)` reduces to `Int.negOfNat b` -- which is **stuck** for a
// symbolic `b`, so `Int.add`'s own four-case split cannot fire either. The two
// stuck terms `add (ofNat a) (negOfNat b)` and `subNatNat a b` are therefore
// NOT definitionally equal, and `Int.ofNat_add_negOfNat` is the theorem that
// bridges them. Once on `subNatNat`, `Int.subNatNat_elim` gives the sign
// dichotomy together with the exact `Nat` equation witnessing it, which is all
// either bound needs:
//
//     ofNat branch : b + k = a, and the goal is about `k`      -> k ≤ a
//     negSucc branch: a + succ k = b, goal about `succ k`      -> succ k ≤ b
//
// so each branch is `magnitude ≤ side` chained with that side's hypothesis.
// The two mirrors differ only in which chaining lemma closes it, which is why
// `coe_sub_coe_bound` takes the relation and the lemma as parameters:
// `Nat.le_trans` and `Nat.lt_of_le_of_lt` have the same shape
// `(x y z) -> le x y -> R y z -> R x z`.
//
// Mathlib proves both through `abs_sub_le_of_nonneg_of_le` and `Nat.cast_le`;
// the route here shares nothing with that and needs no `abs`.

/// `k ≤ j + k`, from `Nat.le_add_right` and one commutation.
///
/// `Nat.le_add_left` does not exist in this prelude; `Nat.le_add_right k j` is
/// `k ≤ k + j`, and `Nat.add` recurses on its RIGHT argument, so the two forms
/// are not interchangeable by reduction.
fn nat_le_add_left(d: &mut IntDev<'_>, k: ExprId, j: ExprId) -> ExprId {
    let right = {
        let name = d.int().nat.le_add_right;
        d.const_app(name, &[k, j])
    };
    let kj = NatOps::add(d, k, j);
    let jk = NatOps::add(d, j, k);
    let comm = {
        let name = d.int().nat.add_comm;
        d.const_app(name, &[k, j])
    };
    d.nat_rewrite(kj, jk, comm, right, &|d, x| d.le(k, x))
}

/// The shared skeleton of both `coe_sub_coe` bounds.
///
/// `relation` builds the conclusion at a magnitude (`Nat.le _ n` or
/// `Nat.lt _ n`); `chain` is the lemma `(x y z) -> le x y -> R y z -> R x z`
/// that closes each branch.
fn coe_sub_coe_bound(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    ha: ExprId,
    hb: ExprId,
    relation: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
    chain: crate::NameId,
) -> ExprId {
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let magnitude = d.nat_abs(x);
        let body = relation(d, magnitude, n);
        let int_ty = d.int_ty();
        d.lam_fv(x_fv, int_ty, body)
    };
    let nat = d.nat_ty();
    // `hof : ∀ k, b + k = a → R k n`. `natAbs (ofNat k)` computes to `k`.
    let hof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let bk = NatOps::add(d, b, k);
        let eq_ty = d.eq(bk, a);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let le_sum = nat_le_add_left(d, k, b);
        let k_le_a = d.nat_rewrite(bk, a, h, le_sum, &|d, x| d.le(k, x));
        let body = d.const_app(chain, &[k, a, n, k_le_a, ha]);
        let inner = d.lam_fv(h_fv, eq_ty, body);
        d.lam_fv(k_fv, nat, inner)
    };
    // `hneg : ∀ k, a + succ k = b → R (succ k) n`.
    // `natAbs (negSucc k)` computes to `succ k`.
    let hneg = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let succ_k = d.succ(k);
        let asum = NatOps::add(d, a, succ_k);
        let eq_ty = d.eq(asum, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let le_sum = nat_le_add_left(d, succ_k, a);
        let sk_le_b = d.nat_rewrite(asum, b, h, le_sum, &|d, x| d.le(succ_k, x));
        let body = d.const_app(chain, &[succ_k, b, n, sk_le_b, hb]);
        let inner = d.lam_fv(h_fv, eq_ty, body);
        d.lam_fv(k_fv, nat, inner)
    };
    let elim = d.int().sub_nat_nat_elim;
    let at_sub_nat_nat = d.const_app(elim, &[motive, a, b, hof, hneg]);
    // Move from `subNatNat a b` to `ofNat a - ofNat b`, which is only
    // PROPOSITIONALLY equal to it -- see this section's header.
    let bridge = {
        let name = d.int().of_nat_add_neg_of_nat;
        d.const_app(name, &[a, b])
    };
    let lhs = d.sub_nat_nat(a, b);
    let rhs = {
        let l = d.of_nat(a);
        let r = d.of_nat(b);
        d.isub(l, r)
    };
    let back = d.isymm(rhs, lhs, bridge);
    d.int_eq_rewrite(lhs, rhs, back, at_sub_nat_nat, &|d, x| {
        let magnitude = d.nat_abs(x);
        relation(d, magnitude, n)
    })
}

/// `nat_abs_coe_sub_coe_le_of_le : ∀ a b n : ℕ, a ≤ n → b ≤ n → natAbs (↑a - ↑b) ≤ n`.
///
/// Mirrors Mathlib's `Int.natAbs_coe_sub_coe_le_of_le`
/// (`Mathlib/Data/Int/Lemmas.lean:69`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_coe_sub_coe_le_of_le(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.nat_abs_coe_sub_coe_le_of_le, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let ha_ty = d.le(a, n);
        let hb_ty = d.le(b, n);
        let concl = {
            let l = d.of_nat(a);
            let r = d.of_nat(b);
            let diff = d.isub(l, r);
            let magnitude = d.nat_abs(diff);
            d.le(magnitude, n)
        };
        let stmt = {
            let inner = d.arrow(hb_ty, concl);
            d.arrow(ha_ty, inner)
        };
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let chain = d.int().nat.le_trans;
        let body = coe_sub_coe_bound(d, a, b, n, ha, hb, &|d, x, y| d.le(x, y), chain);
        let inner = d.lam_fv(hb_fv, hb_ty, body);
        let value = d.lam_fv(ha_fv, ha_ty, inner);
        (stmt, value)
    })?;
    Ok(())
}

/// `nat_abs_coe_sub_coe_lt_of_lt : ∀ a b n : ℕ, a < n → b < n → natAbs (↑a - ↑b) < n`.
///
/// Mirrors Mathlib's `Int.natAbs_coe_sub_coe_lt_of_lt`
/// (`Mathlib/Data/Int/Lemmas.lean:77`). Identical to its `≤` sibling with
/// `Nat.lt_of_le_of_lt` in place of `Nat.le_trans`: each branch still bounds
/// the magnitude by one of `a`, `b` **non-strictly**, and only the outer step
/// is strict.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_coe_sub_coe_lt_of_lt(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.nat_abs_coe_sub_coe_lt_of_lt, 3, &|d, v| {
        let (a, b, n) = (v[0], v[1], v[2]);
        let ha_ty = d.lt(a, n);
        let hb_ty = d.lt(b, n);
        let concl = {
            let l = d.of_nat(a);
            let r = d.of_nat(b);
            let diff = d.isub(l, r);
            let magnitude = d.nat_abs(diff);
            d.lt(magnitude, n)
        };
        let stmt = {
            let inner = d.arrow(hb_ty, concl);
            d.arrow(ha_ty, inner)
        };
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let chain = d.int().nat.lt_of_le_of_lt;
        let body = coe_sub_coe_bound(d, a, b, n, ha, hb, &|d, x, y| d.lt(x, y), chain);
        let inner = d.lam_fv(hb_fv, hb_ty, body);
        let value = d.lam_fv(ha_fv, ha_ty, inner);
        (stmt, value)
    })?;
    Ok(())
}

/// Declare the four `natAbs_inj_of_*` mirrors.
///
/// # Errors
///
/// Returns the trusted gate's rejection if any constructed term does not check.
pub(super) fn declare_nat_abs_inj_mirrors(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_nat_abs_inj_of_nonneg_of_nonneg(d)?;
    declare_nat_abs_inj_of_nonpos_of_nonpos(d)?;
    declare_nat_abs_inj_of_nonneg_of_nonpos(d)?;
    declare_nat_abs_inj_of_nonpos_of_nonneg(d)?;
    declare_mul_self_le_iff(d)?;
    declare_mul_self_lt_iff(d)?;
    declare_mul_self_eq_iff(d)?;
    declare_nat_abs_le_iff_mul_self_le(d)?;
    declare_nat_abs_lt_iff_mul_self_lt(d)?;
    declare_nat_abs_eq_iff_mul_self_eq(d)?;
    declare_nat_abs_coe_sub_coe_le_of_le(d)?;
    declare_nat_abs_coe_sub_coe_lt_of_lt(d)?;
    Ok(())
}
