//! `Nat.avg` and `Nat.pair` — open `Batteries.Data.Nat.Bisect` (`Nat.avg`)
//! and `Mathlib.Data.Nat.Pairing` (`Nat.pair`) for the autogenesis screen.
//!
//! ADR-1045 (draw 12, declined) named this exact unblock: two plain,
//! typeclass-free, `Prod`-free definitions built entirely from existing
//! `Nat.add`/`Nat.mul`/`Nat.div`/`Nat.ble`/`Nat.succ`, and verified by
//! SIMULATION (adding both names to a simulated environment and re-running
//! the real `select()`/`screen_family`) that declaring them opens one
//! 15-candidate held-out family, R9 0/10, R11 fully clean. See
//! `docs/research/09-decisions/adr-1060-declare-nat-avg-and-nat-pair.md`
//! for the re-run of that simulation against this tree, and the
//! post-declaration re-screen.
//!
//! ## `Nat.avg` — no recursor, floor (truncating) division
//!
//! `Nat.avg a b := div (add a b) 2` — Mathlib's/Batteries' own definition
//! (`Batteries.Data.Nat.Bisect`). `Nat.div` here is `nat_prelude`'s total,
//! executable division, which FLOORS: `avg 3 4 = div 7 2 = 3`, not the
//! ceiling `4`. See `avg_pair_tests.rs` for the discriminating check (a
//! rounding-up implementation would fail it).
//!
//! ## `Nat.pair` — the one-directional Cantor-style pairing, no recursor
//!
//! `Nat.pair a b := if a < b then add (mul b b) a else add (add (mul a a)
//! a) b` — Mathlib's own definition (`Mathlib.Data.Nat.Pairing`, also Lean
//! 4 core's `Nat.pair`, the standard injective pairing function used by
//! `Nat.pair`/`Nat.unpair`). `Nat.unpair` (the round-trip inverse) is
//! **not** built here: it returns `Nat × Nat` via `Prod`, which this kernel
//! does not have (ADR-1045 Step 4 confirmed `Nat.unpair`'s pinned signature
//! needs literal `Prod`/`Prod.mk` constants) — only the one-directional
//! `pair` is reachable this way.
//!
//! **CORRECTION (2026-08-31, ADR-1220): that is right about `Nat.unpair` and
//! wrong about the unpairING, and reading it as the latter cost a lane a
//! sizing.** The claim is about a TYPE: Mathlib's `Nat.unpair` returns a
//! product, so *that constant* stays out of reach and every `ml430` mirror
//! stated over it stays `open`. But the two PROJECTIONS have type
//! `Nat → Nat`, which mentions no product — the standing Bool-selected-scalar
//! workaround (`Nat.xgcdAux (sel : Bool)`, `Nat.divModState`) applied one
//! level down. [`super::unpair`] declares them, plus `Nat.unpaired`, whose
//! Mathlib type `(Nat → Nat → Nat) → Nat → Nat` mentions no product either;
//! only the BODY of Mathlib's version needs `unpair`. Its round-trip test
//! inverts THIS module's `Nat.pair` at every argument in `[0,2]²`.
//!
//! The strict order test is built from the kernel's Bool-valued `Nat.ble`:
//! there is no direct Bool `<` primitive, so [`blt`] uses `ble (succ a) b`,
//! definitionally Mathlib's/Lean core's `Nat.blt` and matching `Nat.lt`'s
//! own `Prop` definition `Nat.lt a b := Nat.le (succ a) b` exactly (this
//! prelude's `NatOps::lt`).
//!
//! Neither definition uses `Nat.rec` — both are straight-line applications
//! of already-total primitives (`add`/`mul`/`div`/`ble`/`ite`), so there is
//! no fuel argument, no termination argument, and no argument-recursion
//! order to get backwards.
//!
//! No equation lemma or other theorem is declared here (ADR-0653: the
//! construction and its evaluation test, nothing else) — see
//! `avg_pair_tests.rs` for the concrete instances checked, including the
//! floor-vs-ceiling discriminator for `avg` and the injective-pairing
//! discriminators for `pair` (values a transposed branch condition, a
//! symmetric `x + y` formula, or the textbook two-multiplication Cantor
//! pairing would each get wrong).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Bool-valued `a < b`, i.e. `Nat.ble (succ a) b` — the executable
/// counterpart of `Nat.lt a b := Nat.le (succ a) b` (this prelude's
/// `Prop`-valued `NatOps::lt`), needed here because `Nat.pair`'s branch
/// condition must be a computable `Bool`, not a `Prop`.
fn blt(d: &mut NatDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let sa = d.succ(a);
    d.ble(sa, b)
}

/// Declare `Nat.avg` and `Nat.pair`. Definitions only — see this module's
/// doc for why no theorem about either is declared here.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_avg_pair_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // --- Nat.avg a b := div (add a b) 2 -------------------------------------
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);

        let two = d.num(2);
        let sum = d.add(a, b);
        let body = d.div(sum, two);

        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, with_b)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.avg,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // --- Nat.pair a b := if a < b then b*b+a else a*a+a+b -------------------
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);

        let cond = blt(d, a, b);
        let on_true = {
            let bb = d.mul(b, b);
            d.add(bb, a)
        };
        let on_false = {
            let aa = d.mul(a, a);
            let aa_a = d.add(aa, a);
            d.add(aa_a, b)
        };
        let body = d.bool_select_nat(cond, on_true, on_false);

        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, with_b)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.pair_fn,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    Ok(())
}
