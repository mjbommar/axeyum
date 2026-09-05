//! `Nat.strongInduction` — course-of-values recursion on `Nat`, named
//! (ADR-1614).
//!
//! # Why this is a declaration and not a helper
//!
//! ADR-1608 measured the gap while sizing Hall's marriage theorem: a
//! `shape_search --name-like` sweep for `strong`, `strong_induction` and
//! `le_induction` returns ABSENT at 2,832 declarations, and
//! `Nat.base_induction` is a different statement. What exists is
//! `Nat.lt_well_founded : WellFounded Nat.lt` together with the generic
//! `WellFounded.fix` — enough, but unwrapped, so every caller re-spells the
//! five-argument application and its universe levels. Nine modules in this
//! prelude already do (`base_induction`, `bezout`, `count_range_reversal`,
//! `factorization`, `gcd`, `gcd_mul_right`, `irrational`, `totient_dvd_chain`,
//! `totient_gcd_mul`).
//!
//! ```text
//! Nat.strongInduction.{u} :
//!   ∀ (motive : Nat → Sort u),
//!     (∀ n, (∀ m, Lt m n → motive m) → motive n) → ∀ n, motive n
//!
//! Nat.strongInduction_eq.{u} :
//!   ∀ motive step n,
//!     strongInduction motive step n
//!       = step n (fun m _ => strongInduction motive step m)
//! ```
//!
//! **The motive is explicit, not implicit.** There is no elaborator here — every
//! application is built positionally — so an implicit binder would buy nothing
//! and hide an argument the term builder must supply anyway.
//!
//! **`Sort u`, not `Prop`.** Hall's sufficiency needs a `Prop` motive, but the
//! same wrapper at `Sort u` also covers definitions by course-of-values
//! recursion (the shape `gcd` builds by hand), and `WellFounded.fix` is already
//! universe-polymorphic, so the generality is free.
//!
//! `strongInduction_eq` is `WellFounded.fix_eq` at the same instance: the
//! unfolding equation, which a proof about a strongly-recursive *definition*
//! cannot do without.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Declare `Nat.strongInduction` and its unfolding equation.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_strong_induction_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let u_lvl = d.kernel().level_param(p.cases_on_uparam);
    let sort_u = d.kernel().sort(u_lvl);
    let relation = d.kernel().const_(p.lt, vec![]);
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);

    // `Nat → Sort u`, the motive's type.
    let motive_ty = d.arrow(nat, sort_u);

    // `∀ n, (∀ m, Lt m n → motive m) → motive n`, the step's type.
    let step_ty_at = |d: &mut NatDev<'_>, motive: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let recursive = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let hm_fv = d.fresh_fvar();
            let hm_ty = d.lt(m, n);
            let at_m = d.apply(motive, &[m]);
            let with_hm = d.pi_fv(hm_fv, hm_ty, at_m);
            d.pi_fv(m_fv, nat, with_hm)
        };
        let at_n = d.apply(motive, &[n]);
        let body = d.arrow(recursive, at_n);
        d.pi_fv(n_fv, nat, body)
    };

    // --- Nat.strongInduction ------------------------------------------------
    {
        let motive_fv = d.fresh_fvar();
        let motive = d.kernel().fvar(motive_fv);
        let step_ty = step_ty_at(d, motive);
        let step_fv = d.fresh_fvar();
        let step = d.kernel().fvar(step_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let fix = d
            .kernel()
            .const_(p.logic.well_founded_fix, vec![one, u_lvl]);
        let body = d.apply(fix, &[nat, relation, motive, well_founded, step, n]);

        let ty = {
            let at_n = d.apply(motive, &[n]);
            let with_n = d.pi_fv(n_fv, nat, at_n);
            let with_step = d.arrow(step_ty, with_n);
            d.pi_fv(motive_fv, motive_ty, with_step)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            let with_step = d.lam_fv(step_fv, step_ty, with_n);
            d.lam_fv(motive_fv, motive_ty, with_step)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.strong_induction,
            uparams: vec![p.cases_on_uparam],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // --- Nat.strongInduction_eq ---------------------------------------------
    {
        let motive_fv = d.fresh_fvar();
        let motive = d.kernel().fvar(motive_fv);
        let step_ty = step_ty_at(d, motive);
        let step_fv = d.fresh_fvar();
        let step = d.kernel().fvar(step_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let si = d.kernel().const_(p.strong_induction, vec![u_lvl]);
        let lhs = d.apply(si, &[motive, step, n]);
        let recursive = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let hm_fv = d.fresh_fvar();
            let hm_ty = d.lt(m, n);
            let at_m = d.apply(si, &[motive, step, m]);
            let with_hm = d.lam_fv(hm_fv, hm_ty, at_m);
            d.lam_fv(m_fv, nat, with_hm)
        };
        let rhs = d.apply(step, &[n, recursive]);
        let carrier = d.apply(motive, &[n]);
        let eq_const = d.kernel().const_(p.logic.eq, vec![u_lvl]);
        let concl = d.apply(eq_const, &[carrier, lhs, rhs]);

        let fix_eq = d
            .kernel()
            .const_(p.logic.well_founded_fix_eq, vec![one, u_lvl]);
        let body = d.apply(fix_eq, &[nat, relation, motive, well_founded, step, n]);

        let ty = {
            let with_n = d.pi_fv(n_fv, nat, concl);
            let with_step = d.pi_fv(step_fv, step_ty, with_n);
            d.pi_fv(motive_fv, motive_ty, with_step)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            let with_step = d.lam_fv(step_fv, step_ty, with_n);
            d.lam_fv(motive_fv, motive_ty, with_step)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.strong_induction_eq,
            uparams: vec![p.cases_on_uparam],
            ty,
            value,
        })?;
    }

    Ok(())
}
