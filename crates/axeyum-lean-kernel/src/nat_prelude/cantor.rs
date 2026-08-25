//! Cantor's diagonal argument, stated pointwise over `Nat → Bool` sequences.
//!
//! # Why the textbook statement is unavailable, and what replaces it
//!
//! The usual phrasing says a diagonal function `g` is **not equal to any
//! row**: `∀ f : Nat → Nat → Bool, ∃ g, ∀ n, g ≠ f n`. Proving `g ≠ f n` as an
//! equality of *functions* needs function extensionality to relate that
//! inequality to a witnessed pointwise difference — and `funext` is banned in
//! this kernel (no `Classical.em`, `propext`, `funext`, `Quot.sound`
//! anywhere in a proof). So the function-level statement is simply not
//! available here: proving it is off the table, and so is refuting it.
//!
//! The pointwise statement below is *stronger* than the function-level one
//! (it exhibits the differing index directly) and needs no extensionality at
//! all:
//!
//! ```text
//! Nat.cantor_diagonal :
//!   ∀ f : Nat → Nat → Bool, ∃ g : Nat → Bool, ∀ n, Eq Bool (g n) (f n n) → False
//! ```
//!
//! with witness `g := fun n => not (f n n)`. Each row `f n` is wrong about
//! its own index `n`, so no `f` enumerates every `Nat → Bool` sequence: for
//! every candidate `f`, [`declare_cantor_diagonal`] hands back a `g` that
//! every row misses at its own diagonal position.
//!
//! # `Exists` over a function-typed witness
//!
//! The existential's witness type is `α := Nat → Bool`, not `Nat`. This
//! works, and it is worth saying exactly why, because [`super::diagonal`]'s
//! module doc documents the *opposite* direction failing for the same
//! inductive: `Exists.rec` cannot *extract* a witness of the wrong sort,
//! because `allows_large_elimination` is `false` for `Exists` (its witness
//! field is not one of its own indices — `Exists` has none), so the
//! generated `Exists.rec` only eliminates into a `Prop` motive.
//!
//! That restriction is about the **eliminator**, `Exists.rec`. It says
//! nothing about `Exists` and `Exists.intro` themselves, and their stated
//! types are unconditional in `α`:
//!
//! ```text
//! Exists.{u}       : ∀ (α : Sort u), (α → Prop) → Prop
//! Exists.intro.{u} : ∀ (α : Sort u) (p : α → Prop) (w : α), p w → Exists α p
//! ```
//!
//! `α` ranges over an arbitrary `Sort u`; nothing restricts it to `Nat`. Here
//! `α := Nat → Bool`. `Nat` and `Bool` are both rendered as real Lean
//! `inductive`s at `Sort 1` (`Type`), and a non-dependent Pi type's universe
//! is `imax` of its domain's and codomain's universes — `imax 1 1 = 1` — so
//! `Nat → Bool : Sort 1` too, exactly the universe every other use of
//! `Exists`/`Exists.intro` in this prelude already instantiates `u` at (see
//! e.g. `ops.rs`'s `bezout_intro`, always `α := Nat`). So `Exists.{1} (Nat →
//! Bool) pred` and `Exists.intro.{1} (Nat → Bool) pred g h` both type-check
//! at the *same* universe level a first-order existential over `Nat` does —
//! packaging a whole function as a witness costs nothing in universe terms
//! here, because the packaging (`Exists.intro`) is a plain constructor
//! application, not an elimination. The kernel never has to look *inside*
//! `g` to accept the proof; it only has to check `g : Nat → Bool` and `h : pred
//! g`, both ordinary type-checking obligations.
//!
//! This kernel's `Exists` therefore *can* express "there exists a sequence
//! with property P" — the finding the handover asked to pin down precisely —
//! even though it cannot, and never will be asked to, *compute* that sequence
//! back out of the proof term. Building (`Exists.intro`) and consuming
//! (`Exists.rec`) are independent capabilities here, and only the second is
//! constrained.
//!
//! # The case split, and why it is constructive
//!
//! The only step needed per index is deciding `g n` vs `f n n`, i.e.
//! `not b` vs `b` for `b := f n n : Bool`. `Bool` is a two-constructor
//! inductive (`Bool.false | Bool.true`, official Lean order), so `Bool.rec`
//! gives a genuine case split with no appeal to excluded middle:
//! [`cantor_pointwise`] eliminates `b` into the *Prop* motive `fun x => Eq
//! Bool (not x) x → False` and discharges each of the two branches with one
//! of the logic prelude's own `Bool` disjointness facts,
//! [`crate::LogicPrelude::bool_true_ne_false`] /
//! [`crate::LogicPrelude::bool_false_ne_true`], once `not` ι-reduces on the
//! constructor at hand. Both are theorems with an empty axiom footprint, so
//! [`declare_cantor_diagonal`]'s own footprint is empty too.
//!
//! `not : Bool → Bool` itself is not declared as a separate public name here
//! (this prelude has no `Nat.not`/`Bool.not` yet) — [`not_bool`] builds the
//! term `Bool.rec (fun _ => Bool) Bool.true Bool.false b` inline, exactly
//! [`super::finite_set`]'s private `bool_select_bool` specialized to swap the
//! two constructors (that helper is not `pub(super)`, so this module carries
//! its own copy — the same per-file convention `finite_set.rs` documents for
//! itself).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `not b := Bool.rec (fun _ => Bool) Bool.true Bool.false b` — computational
/// Boolean negation, inline (not a declared name). Reduces by ι:
/// `not Bool.false ≡ Bool.true`, `not Bool.true ≡ Bool.false`.
fn not_bool(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    // `fun (_ : Bool) => Bool` — the type-valued, non-dependent motive
    // `bool_select_bool`-style constructions all share; built via `lam_fv`
    // with a dummy free variable that never occurs in the body, so
    // abstraction is a no-op and this is exactly that lambda.
    let motive_fv = d.fresh_fvar();
    let motive = d.lam_fv(motive_fv, bool_ty, bool_ty);
    let one = d.level_one();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    // [motive, on_false, on_true, condition]; `not true = false`, `not false
    // = true`, so the "true" minor premise is `false_` and vice versa.
    d.apply(bool_rec, &[motive, true_, false_, b])
}

/// `Eq Bool (not b) b → False`, for arbitrary `b : Bool` — proved by a
/// `Bool.rec` case split into a `Prop` motive (constructive: two
/// constructors, not excluded middle). Each branch collapses to one of the
/// logic prelude's `Bool` disjointness facts once `not` ι-reduces on the
/// constructor the branch fixes `b` to.
fn cantor_pointwise(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let false_const = d.kernel().const_(p.logic.false_, vec![]);

    // `fun (x : Bool) => Eq Bool (not x) x → False`.
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let not_x = not_bool(d, p, x);
        let eq_ty = d.bool_eq(not_x, x);
        let neg_ty = d.arrow(eq_ty, false_const);
        d.lam_fv(x_fv, bool_ty, neg_ty)
    };

    // x = Bool.false: `not false` ι-reduces to `true`, so the branch needs
    // `Eq Bool true false → False`, exactly `bool_true_ne_false`.
    let case_false = d.kernel().const_(p.logic.bool_true_ne_false, vec![]);
    // x = Bool.true: `not true` ι-reduces to `false`, so the branch needs
    // `Eq Bool false true → False`, exactly `bool_false_ne_true`.
    let case_true = d.kernel().const_(p.logic.bool_false_ne_true, vec![]);

    let zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// `Nat.cantor_diagonal : ∀ f : Nat → Nat → Bool,
///   ∃ g : Nat → Bool, ∀ n, Eq Bool (g n) (f n n) → False`
///
/// Witness `g := fun n => not (f n n)`; see the module doc for the
/// `Exists`-over-a-function-type justification and for why this pointwise
/// form replaces the (unavailable, funext-shaped) function-level statement.
pub(super) fn declare_cantor_diagonal(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let false_const = d.kernel().const_(p.logic.false_, vec![]);
    let one = d.level_one();

    let row_ty = d.arrow(nat, bool_ty); // Nat -> Bool
    let fn2_ty = d.arrow(nat, row_ty); // Nat -> Nat -> Bool

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    // `pred := fun g => ∀ n, Eq Bool (g n) (f n n) → False`.
    let pred = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let gn = d.apply(g, &[n]);
            let fnn = d.apply(f, &[n, n]);
            let eq_ty = d.bool_eq(gn, fnn);
            let neg_ty = d.arrow(eq_ty, false_const);
            d.pi_fv(n_fv, nat, neg_ty)
        };
        d.lam_fv(g_fv, row_ty, body)
    };

    let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
    let stmt_for_f = d.apply(exists_c, &[row_ty, pred]);

    // The witness `g := fun n => not (f n n)`.
    let g_term = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fnn = d.apply(f, &[n, n]);
        let not_fnn = not_bool(d, &p, fnn);
        d.lam_fv(n_fv, nat, not_fnn)
    };

    // The proof `∀ n, Eq Bool (not (f n n)) (f n n) → False`.
    let h_forall = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fnn = d.apply(f, &[n, n]);
        let proof_n = cantor_pointwise(d, &p, fnn);
        d.lam_fv(n_fv, nat, proof_n)
    };

    let intro_c = d.kernel().const_(p.logic.exists_intro, vec![one]);
    let ex_proof = d.apply(intro_c, &[row_ty, pred, g_term, h_forall]);

    let ty = d.pi_fv(f_fv, fn2_ty, stmt_for_f);
    let value = d.lam_fv(f_fv, fn2_ty, ex_proof);

    d.declare_theorem(p.cantor_diagonal, ty, value)
}

/// Declare this module's result.
pub(super) fn declare_cantor_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_cantor_diagonal(d, p)
}
