//! `Nat.findGreatest` — opens `Mathlib.Data.Nat.Find` for the autogenesis
//! screen at cycle index 3.
//!
//! ADR-1160 (this lane). Four consecutive draws declined. ADR-1095 measured
//! the mechanism (`assign_partitions` assigns `held-out` only at cycle index
//! `0, 3, 6, …`, so R5's two-held-out minimum needs four fresh families);
//! ADR-1100 corrected the framing from counting to POSITION (index 3 is the
//! scarce slot, because everything constructible with no new work sorts early
//! by first Mathlib module name); ADR-1115 declined draw 14 because the one
//! late family available, `natural-factorisation-properties`, draws two rows
//! (`Nat.Abundant 12`, `Nat.Deficient 1`) that ADR-1100's own construction
//! settles by reduction, and widened R12's `is_closed_evaluation` so that a
//! ground PREDICATE application is visible to the gate at last.
//!
//! This module is the next index-3 family. `Mathlib.Data.Nat.Find` sorts after
//! every free family, its topic segment (`Find`) is published by no
//! development/train family, and with `DecidablePred` and `Nat.findGreatest`
//! declared its pool is 15 rows — R5, R9, R12 and R11's topic and vocabulary
//! signals all clean against the real `select()`/`guard()`. See the ADR for
//! the full nine-candidate screen.
//!
//! ## What the drawn ten are, and why none of them is settled here
//!
//! The alphabetically-first ten rows the draw would take are
//! `findGreatest_eq`, `_eq_iff`, `_eq_zero_iff`, `_is_greatest`, `_le`,
//! `_mono`, `_mono_left`, `_mono_right`, `_of_ne_zero`, `_of_not`. Every one
//! carries binders over the predicate `P`, so none is a closed evaluation
//! under either shape R12 classifies, and none is provable by `Eq.refl`
//! against this definition: `dp (succ m)` is a variable applied to a term, so
//! the `Decidable.byCases` never ι-reduces and the recursion is stuck at every
//! symbolic argument.
//!
//! **What IS settled here, disclosed rather than left to be found:** the pool's
//! rows 12 and 13, `Nat.findGreatest_succ` and `Nat.findGreatest_zero`, are
//! this definition's own two equations and would be `Eq.refl` (modulo Lean's
//! `ite` against our `Decidable.byCases`). They fall outside the drawn ten by
//! the alphabet alone — not by any choice made here, and no module was added
//! or removed to put them there, which is the move ADR-1115 rules out on
//! principle. A draw lane that COMBINES `Mathlib.Data.Nat.Find` with another
//! module changes which ten are drawn and must re-run the screen; a family
//! over this module alone is what was measured.
//!
//! Note also what R12 cannot see about them: both statements are
//! `∀ {P} [DecidablePred P], …`, so `_ground_shape` rejects them for having
//! binders and the widened classifier would report them clean even if they
//! WERE drawn. The pre-declaration check ADR-1115 prescribes therefore has to
//! be a reading of the pool as well as a run of the classifier.
//!
//! ## The definition, and why the mirror stays open
//!
//! Mathlib (`Mathlib/Order/Basic.lean` re-exported through
//! `Mathlib.Data.Nat.Find`):
//!
//! ```text
//! def Nat.findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
//!   | 0     => 0
//!   | n + 1 => if P (n + 1) then n + 1 else Nat.findGreatest P n
//! ```
//!
//! Ours is the same structural recursion, with two surface differences forced
//! by this kernel rather than chosen:
//!
//! * the `DecidablePred` witness is an EXPLICIT argument, because there are no
//!   instance implicits here, so the type is
//!   `Π (P : Nat → Prop), DecidablePred Nat P → Nat → Nat` rather than
//!   Mathlib's `(ℕ → Prop) → ℕ → ℕ`; and
//! * the branch is `Decidable.byCases.{1}` rather than `ite`, which this
//!   kernel does not declare. `ite` IS `Decidable.byCases` with the two
//!   branches constant, so the two agree wherever both are defined.
//!
//! Per `CLAUDE.md`'s mirror-flip criterion this is the `Nat.nth`/`Nat.minFac`
//! case and not the `Nat.descFactorial_of_lt` case: the definitional bodies
//! agree extensionally but the TYPES differ, so every `ml430` mirror stated
//! against Mathlib's `Nat.findGreatest` stays `open`, and a theorem about THIS
//! one would need its own `F:nat-*` fact.
//!
//! ## No theorems
//!
//! ADR-0653: an unblocking lane declares the construction and its evaluation
//! test and NOTHING else. The lane that also declared seven ordinary
//! supporting theorems had its family refused by R9 as no longer blind; its
//! sibling, which declared the construction only, survived. Everything useful
//! about `findGreatest` can land tomorrow from `development`.
//!
//! ## Why the evaluation test is not optional
//!
//! `Nat → Nat` is `Nat → Nat` whatever the function returns, so
//! `add_declaration` accepts a wrong recursion as readily as the intended one.
//! The specific failures available here are a swapped `byCases` pair (the
//! predicate tested and then IGNORED, returning `ih` when it should return
//! `succ m`), an off-by-one in the tested argument (`m` rather than `succ m`),
//! and a base case returning something other than `0`.
//! `find_greatest_tests.rs` discriminates all three at concrete arguments,
//! against a predicate true at exactly one point.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// Declare `Nat.findGreatest`. A definition only — see this module's doc for
/// why no theorem about it is declared here.
///
/// Depends on the logic prelude's `DecidablePred` and `Decidable.byCases`
/// (`prelude.rs`); nothing in `nat_prelude` has to run first.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_find_greatest_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    // `P : Nat -> Prop`.
    let pred_ty = d.arrow(nat, prop);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);

    // `DecidablePred.{1} Nat P` -- the witness type. `Nat : Sort 1`, so the
    // universe argument is `1` and the result lands in `Sort (max 1 1)`.
    let witness_ty = {
        let head = d.kernel().const_(p.logic.decidable_pred, vec![one]);
        d.apply(head, &[nat, pred])
    };
    let witness_fv = d.fresh_fvar();
    let witness = d.kernel().fvar(witness_fv);

    // motive := fun (_ : Nat) => Nat.
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);

    // base := 0. Mathlib's own base case, and it does NOT test `P 0`:
    // `findGreatest P 0 = 0` even when `P 0` holds. The test file pins that.
    let base = d.zero();

    // step := fun m ih => Decidable.byCases.{1} (P (succ m)) Nat
    //   (witness (succ m)) (fun _ => succ m) (fun _ => ih).
    let step = {
        let m_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let ih = d.kernel().fvar(ih_fv);

        let sm = d.succ(m);
        let p_at_sm = d.apply(pred, &[sm]);
        let decision = d.apply(witness, &[sm]);

        // `p -> Nat`: the hypothesis is discarded, so a non-dependent `lam`.
        let on_true = d.kernel().lam(anon, p_at_sm, sm, BinderInfo::Default);
        let refutation_ty = {
            let false_const = d.kernel().const_(p.logic.false_, vec![]);
            d.arrow(p_at_sm, false_const)
        };
        let on_false = d
            .kernel()
            .lam(anon, refutation_ty, ih, BinderInfo::Default);

        let by_cases = d.kernel().const_(p.logic.decidable_by_cases, vec![one]);
        let body = d.apply(by_cases, &[p_at_sm, nat, decision, on_true, on_false]);

        let with_ih = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(m_fv, nat, with_ih)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec = d.kernel().const_(p.rec, vec![one]);
    let applied = d.apply(rec, &[motive, base, step, n]);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, applied);
        let with_witness = d.lam_fv(witness_fv, witness_ty, with_n);
        d.lam_fv(pred_fv, pred_ty, with_witness)
    };
    let ty = {
        let over_n = d.arrow(nat, nat);
        let over_witness = d.arrow(witness_ty, over_n);
        d.pi_fv(pred_fv, pred_ty, over_witness)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.find_greatest,
        uparams: vec![],
        ty,
        value,
        // Above `Nat.succ`, the only `Nat` definition it calls;
        // `Decidable.byCases` and `DecidablePred` carry their own heights in
        // the logic prelude.
        hint: ReducibilityHint::Regular(5),
    })?;

    Ok(())
}
