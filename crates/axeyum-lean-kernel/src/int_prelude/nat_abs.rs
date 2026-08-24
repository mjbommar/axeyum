//! `Int.natAbs` — the magnitude of an integer as a natural number.
//!
//! The first piece of the ℚ groundwork. Lean core's `Rat` is a structure whose
//! coprimality field is stated as `num.natAbs.Coprime den`, so a rational
//! normalised by `gcd` needs the numerator's magnitude in `ℕ` before anything
//! else can be said about it. See
//! [`docs/mathematics-2026-08/02-the-library.md`] for why ℚ is built as a
//! normalised structure rather than the setoid quotient the strand originally
//! named — this kernel has no `Quot.sound`, and Lean itself does not use one.
//!
//! The definition is one `Int.rec`, and both computation rules hold by `rfl`:
//!
//! ```text
//! Int.natAbs (ofNat n)   ≡ n
//! Int.natAbs (negSucc m) ≡ succ m
//! ```
//!
//! The one lemma with content is [`of_nat_nat_abs_of_nonneg`]: on a non-negative
//! integer the magnitude round-trips. Its negative branch is discharged by
//! absurdity rather than by arithmetic, because `Int.le (ofNat 0) (negSucc n)`
//! *reduces* to `False`.

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{BinderInfo, ExprId};
// `NatOps` carries the shared term-building surface (`kernel`, `nat_ty`,
// `level_one`, `anon_name`, `succ`) that `IntDev` implements.
use crate::nat_prelude::NatOps;

use super::ops::{IntDev, Shape, case_split};

/// Height for the `Int.natAbs` definition: it unfolds to one recursor
/// application over `Nat`, so it sits with the other derived operations.
const DERIVED_HEIGHT: u16 = 4;

/// Admit `Int.natAbs : Int → Nat`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();

    let motive = d.kernel().lam(anon, int_ty, nat, BinderInfo::Default);
    let minor_of = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, n)
    };
    let minor_neg = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = d.succ(m);
        d.lam_fv(m_fv, nat, body)
    };
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let rec = d.kernel().const_(p.rec, vec![one]);
    let body = d.apply(rec, &[motive, minor_of, minor_neg, a]);
    let value = d.lam_fv(a_fv, int_ty, body);
    let ty = {
        let nat_ty = d.nat_ty();
        d.arrow(int_ty, nat_ty)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.nat_abs,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })?;
    Ok(())
}

/// `nat_abs_neg_of_nat : ∀ (k : Nat), natAbs (negOfNat k) = k`.
///
/// `negOfNat` is a `Nat.rec` definition, so it does **not** reduce on a
/// variable — measured, not assumed. Under a case split it does: `negOfNat 0` is
/// `ofNat 0` and `negOfNat (succ j)` is `negSucc j`, and `natAbs` computes on
/// both constructors, so each branch closes by `rfl`.
///
/// The `negSucc` branch of `Rat.normalize` needs this: it builds its numerator
/// with `negOfNat` and must then say what the `reduced` field is about.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_neg_of_nat(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let claim = |d: &mut IntDev<'_>, x: ExprId| {
        let negated = d.neg_of_nat(x);
        let magnitude = d.nat_abs(negated);
        d.eq(magnitude, x)
    };
    let at_zero = |d: &mut IntDev<'_>| {
        let zero = d.zero();
        d.refl(zero)
    };
    let at_succ = |d: &mut IntDev<'_>, j: ExprId, _ih: ExprId| {
        let successor = d.succ(j);
        d.refl(successor)
    };
    let value = d.induct(&claim, &at_zero, &at_succ, k);

    let ty = {
        let body = claim(d, k);
        d.pi_fv(k_fv, nat, body)
    };
    let value = d.lam_fv(k_fv, nat, value);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.nat_abs_neg_of_nat,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

/// `of_nat_nat_abs_of_nonneg : 0 ≤ a → ofNat (natAbs a) = a`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_lemmas(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.of_nat_nat_abs_of_nonneg, 1, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let a = args[0];
            let zero = d.izero();
            let hypothesis = d.ile(zero, a);
            let magnitude = d.nat_abs(a);
            let lifted = d.of_nat(magnitude);
            let conclusion = d.ieq(lifted, a);
            d.arrow(hypothesis, conclusion)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, b| {
            let magnitude = b[0].1;
            match b[0].0 {
                // `natAbs (ofNat n)` is `n`, so the goal is `ofNat n = ofNat n`
                // once the hypothesis is bound; nothing to prove but refl.
                Shape::OfNat => {
                    let value = d.of_nat(magnitude);
                    let zero = d.izero();
                    let hypothesis = d.ile(zero, value);
                    let refl = d.irefl(value);
                    let h_fv = d.fresh_fvar();
                    d.lam_fv(h_fv, hypothesis, refl)
                }
                // `0 ≤ negSucc n` REDUCES to `False`, so the hypothesis is the
                // proof that this branch is unreachable.
                Shape::NegSucc => {
                    let value = d.neg_succ(magnitude);
                    let zero = d.izero();
                    let hypothesis = d.ile(zero, value);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let lifted = {
                        let inner = d.nat_abs(value);
                        d.of_nat(inner)
                    };
                    let goal = d.ieq(lifted, value);
                    let body = d.absurd(goal, h);
                    d.lam_fv(h_fv, hypothesis, body)
                }
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `natAbs` applied, for use inside this module's statements.
trait NatAbsOps {
    fn nat_abs(&mut self, a: ExprId) -> ExprId;
}

impl NatAbsOps for IntDev<'_> {
    fn nat_abs(&mut self, a: ExprId) -> ExprId {
        let name = self.int().nat_abs;
        self.const_app(name, &[a])
    }
}

/// `nat_abs_neg : ∀ (n : Int), natAbs (neg n) = natAbs n`.
///
/// Negation preserves magnitude. `Rat.neg` needs it: negating a numerator must
/// leave the `reduced` field provable, and that field speaks of `natAbs`.
///
/// Both branches are cheap once split. `neg (ofNat k)` is `negOfNat k`, so the
/// goal is [`declare_nat_abs_neg_of_nat`]; `neg (negSucc k)` is `ofNat (succ k)`
/// and `natAbs` computes on both sides, so it is `rfl`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_neg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.nat_abs_neg, 1, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let a = args[0];
            let negated = d.ineg(a);
            let left = d.nat_abs(negated);
            let right = d.nat_abs(a);
            d.eq(left, right)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, b| {
            let magnitude = b[0].1;
            match b[0].0 {
                // `neg (ofNat k)` is `negOfNat k`, and `natAbs (ofNat k)` is `k`.
                Shape::OfNat => d.const_app(p.nat_abs_neg_of_nat, &[magnitude]),
                // `neg (negSucc k)` is `ofNat (succ k)`; both sides compute to
                // `succ k`.
                Shape::NegSucc => {
                    let successor = d.succ(magnitude);
                    d.refl(successor)
                }
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `nat_abs_pow : ∀ (a : Int) (k : Nat), Eq Nat (natAbs (pow a k)) (Nat.pow
/// (natAbs a) k)` — the magnitude of a power is the power of the magnitude,
/// by induction on `k` through [`super::gcd`]'s `nat_abs_mul` and `Nat`'s own
/// `pow_succ`.
///
/// A `Nat`-typed equation (both sides are `Nat`), unlike every other law in
/// this module. Quantifies over one `Int` and one `Nat`, so it is declared
/// by hand rather than through
/// [`IntDev::int_theorem`](super::ops::IntDev::int_theorem), the same reason
/// `Int.pow_succ`/`Int.pow_add` are (`defs.rs`, `algebra.rs`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_nat_abs_pow(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let pow_a_x = d.ipow(a, x);
        let lhs = d.nat_abs(pow_a_x);
        let nat_abs_a = d.nat_abs(a);
        let rhs = d.pow(nat_abs_a, x);
        d.eq(lhs, rhs)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let stmt_inner = motive(d, k);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let one = d.num(1);
            d.refl(one)
        },
        &|d, j, ih| {
            // `natAbs (a^(succ j))` computes to `natAbs (a^j * a)`.
            let pow_a_j = d.ipow(a, j);
            let mul_term = d.imul(pow_a_j, a);
            let start = d.nat_abs(mul_term);
            let nat_abs_pow_j = d.nat_abs(pow_a_j);
            let nat_abs_a = d.nat_abs(a);
            let after_split = d.mul(nat_abs_pow_j, nat_abs_a);
            let h_split = d.const_app(p.nat_abs_mul, &[pow_a_j, a]);

            let nat_abs_a_pow_j = d.pow(nat_abs_a, j);
            let after_ih = d.mul(nat_abs_a_pow_j, nat_abs_a);
            let h_ih = d.congr(nat_abs_pow_j, nat_abs_a_pow_j, ih, &|d, t| {
                d.mul(t, nat_abs_a)
            });

            let succ_j = d.succ(j);
            let end_term = d.pow(nat_abs_a, succ_j);
            let pow_succ_name = d.prelude().pow_succ;
            let h_pow_succ = d.const_app(pow_succ_name, &[nat_abs_a, j]);
            let h_pow_succ_rev = d.symm(end_term, after_ih, h_pow_succ);

            let (_, proof) = d.chain(
                start,
                &[
                    (after_split, h_split),
                    (after_ih, h_ih),
                    (end_term, h_pow_succ_rev),
                ],
            );
            proof
        },
        k,
    );

    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt_inner);
        d.pi_fv(a_fv, int_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof_inner);
        d.lam_fv(a_fv, int_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.nat_abs_pow,
        uparams: vec![],
        ty,
        value,
    })
}
