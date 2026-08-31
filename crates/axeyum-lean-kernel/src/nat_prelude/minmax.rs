//! `Max.max`, `Min.min`, `Nat.instMax`, `instMinNat` — open
//! `Init.Data.Nat.MinMax` for the autogenesis screen. ADR-1045 (draw 12,
//! declined) named this as the largest remaining opportunity (30 candidate
//! rows) and flagged it as the HARDER route because Mathlib states every
//! `MinMax` lemma through the `Max`/`Min` typeclass rather than as a plain
//! `Nat.max`/`Nat.min` function — the missing constants in the pinned
//! inventory's raw `Lean.Expr` dump are literally `Max.max`, `Min.min`,
//! `Nat.instMax`, `instMinNat` (the elaborated typeclass method plus its
//! `Nat` instance, for each of `Max`/`Min`).
//!
//! ADR-1060 re-ran the real `select()`/`admissible()`/`screen_family` with
//! these four bare-root names added to a simulated environment (not by
//! inspection) and confirmed: 32 module rows, 30 admissible once all four
//! names exist, R9 0/10 against the real environment, R11 fully clean with
//! **zero** environment-sweep hits (cleaner than `avg_pair.rs`'s own
//! screen, which had one advisory hit on its own name). See that ADR for
//! the transcript.
//!
//! ## Bare-root and cross-namespace names, not `Nat.max`/`Nat.min`
//!
//! This kernel has no typeclasses (ADR-1045 Step 4; the only inductives are
//! the fixed list in `docs/research/…` plus `Nat.Pair`/`Nat.Fin`), so there
//! is no `Max`/`Min` class and no real instance-resolution mechanism to
//! reconstruct. The autogenesis screen's admissibility test is purely
//! SYNTACTIC — it extracts literal constant tokens from Mathlib's own raw
//! `Lean.Expr` dump and checks each is a name in `kernel.environment()` (or
//! the derived bridge vocabulary) — so what unblocks the screen is a kernel
//! declaration whose RENDERED NAME matches the literal token, independent
//! of whether its type mirrors Mathlib's typeclass-polymorphic signature.
//! [`squarefree.rs`](super::squarefree) already established this pattern
//! for a bare-root name (`Squarefree`, not `Nat.squarefree`); this module
//! extends it to FOUR names across three different namespace roots (`Max`,
//! `Min`, `Nat`, and the bare root itself for `instMinNat`), because that
//! is exactly the shape the pinned inventory's constant tokens use:
//!
//! | our declaration | namespace | Mathlib's role |
//! |---|---|---|
//! | `Max.max`     | `Max` (new root) | the `Max` class's method, monomorphic here at `Nat -> Nat -> Nat` |
//! | `Min.min`     | `Min` (new root) | the `Min` class's method, same shape |
//! | `Nat.instMax` | `Nat`            | the elaborated `Max Nat` instance argument Mathlib's statements apply `Max.max` to |
//! | `instMinNat`  | bare root        | the elaborated `Min Nat` instance argument (Mathlib's own name has no namespace prefix) |
//!
//! **`Nat.instMax`/`instMinNat` are NOT real typeclass instances** — this
//! kernel has no `Max`/`Min` structure type to be an instance OF, so there
//! is nothing to construct that could carry that meaning. They are declared
//! here as ordinary `Nat -> Nat -> Nat` functions, definitionally EQUAL to
//! `Max.max`/`Min.min` (not merely propositionally — `Nat.instMax a b`
//! reduces to `Max.max a b` by unfolding, so both compute the SAME correct
//! value; see `minmax_tests.rs`). This mirrors `nth.rs`'s and
//! `squarefree.rs`'s precedent exactly: a declaration under Mathlib's exact
//! name, with a genuinely different TYPE than Mathlib's own definition
//! (there Mathlib's is `Prop`/dependent-motive-shaped; here Mathlib's is a
//! typeclass method/instance pair). Any mirror theorem stated against
//! Mathlib's REAL, typeclass-elaborated `Max.max`/`Min.min` stays `open`
//! for the same reason — this module only opens the vocabulary; it proves
//! nothing about Mathlib's typeclass machinery.
//!
//! ## Semantics, and why the branch is on `Nat.ble`
//!
//! `Max.max a b := if a <= b then b else a`, `Min.min a b := if a <= b
//! then a else b` — the standard total-order max/min, using this
//! prelude's Bool-valued `Nat.ble` (matching [`avg_pair.rs`](super::avg_pair)'s
//! `blt` device but without needing the `succ` shift, since `<=` is what
//! `Nat.ble` already computes directly). Both branches are exercised by
//! `minmax_tests.rs`'s concrete instances, including the `a == b` boundary
//! where `Nat.ble a b` is `true` and either branch would give the same
//! answer by coincidence — not proof that the branch selection is right in
//! general, which is why the tests also cover both strict orderings.
//!
//! Neither definition uses `Nat.rec` — both are straight-line applications
//! of already-total primitives (`ble`/`ite`), so there is no fuel argument,
//! no termination argument, and no argument-recursion order to get
//! backwards.
//!
//! No equation lemma or other theorem is declared here (ADR-0653: the
//! construction and its evaluation test, nothing else) — see
//! `minmax_tests.rs` for the concrete instances checked.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Max.max a b := if a <= b then b else a`.
fn build_max(d: &mut NatDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let le = d.ble(a, b);
    d.bool_select_nat(le, b, a)
}

/// `Min.min a b := if a <= b then a else b`.
fn build_min(d: &mut NatDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let le = d.ble(a, b);
    d.bool_select_nat(le, a, b)
}

/// Declare `Max.max`, `Min.min`, `Nat.instMax`, `instMinNat`. Definitions
/// only — see this module's doc for why no theorem about any of them is
/// declared here.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_minmax_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let binop_ty = {
        let inner = d.arrow(nat, nat);
        d.arrow(nat, inner)
    };

    // --- Max.max a b := if a <= b then b else a -----------------------------
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = build_max(d, a, b);
        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, with_b)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.max_max,
            uparams: vec![],
            ty: binop_ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // --- Min.min a b := if a <= b then a else b -----------------------------
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = build_min(d, a, b);
        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, with_b)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.min_min,
            uparams: vec![],
            ty: binop_ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // --- Nat.instMax a b := Max.max a b -------------------------------------
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = d.const_app(p.max_max, &[a, b]);
        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, with_b)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.nat_inst_max,
            uparams: vec![],
            ty: binop_ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // --- instMinNat a b := Min.min a b --------------------------------------
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = d.const_app(p.min_min, &[a, b]);
        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, with_b)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.inst_min_nat,
            uparams: vec![],
            ty: binop_ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    Ok(())
}
