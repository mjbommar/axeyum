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
