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
    Ok(())
}
