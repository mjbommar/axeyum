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

/// `Nat.cantor_diagonal_neg : ∀ f : Nat → Nat → Bool,
///   (∀ g : Nat → Bool, ∃ n, ∀ k, Eq Bool (f n k) (g k)) → False`
///
/// The negative form the handover asked for, in the exact pointwise shape it
/// suggested: no `f` enumerates every `Nat → Bool` sequence, where
/// "enumerates" is stated as `∀ k, Eq Bool (f n k) (g k)` rather than an
/// equality of functions `f n = g` (which would need `funext`). This form —
/// not `¬ ∃ g, ∀ n, …` or any other shuffling of the quantifiers — is the one
/// that follows directly from [`declare_cantor_diagonal`] with no further
/// principles: assume the hypothesis `h`, instantiate [`Self::cantor_diagonal`]
/// at `f` to get some `g₀` that disagrees with every row at its own index,
/// apply `h` to that *same* `g₀` to get a row `n₀` claiming to agree with
/// `g₀` everywhere, specialize that agreement at `k := n₀`, and the two facts
/// contradict (via `Eq.symm`, since the two equalities are stated in opposite
/// orders).
///
/// Both existentials here — [`Self::cantor_diagonal`]'s own and `h`'s — are
/// eliminated by nested `Exists.rec` into the `Prop` motive `fun _ => False`.
/// Each minor premise binds *both* the witness (`g₀`, then `n₀`) and the
/// hypothesis about it, which is the discipline the handover flagged as the
/// place a nested `Exists.rec` chain goes wrong (an inner witness left
/// unbound reads as `UnboundFVar` only when the whole environment is
/// re-verified, not at the point the term was built).
pub(super) fn declare_cantor_diagonal_neg(
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

    // hyp_ty := ∀ g : Nat -> Bool, ∃ n, ∀ k, Eq Bool (f n k) (g k)
    let (g_fv, hyp_body_ty) = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let inner_pred = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let fnk = d.apply(f, &[n, k]);
                let gk = d.apply(g, &[k]);
                let eq_ty = d.bool_eq(fnk, gk);
                d.pi_fv(k_fv, nat, eq_ty)
            };
            d.lam_fv(n_fv, nat, body)
        };
        let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
        let ex_ty = d.apply(exists_c, &[nat, inner_pred]);
        (g_fv, ex_ty)
    };
    let hyp_ty = d.pi_fv(g_fv, row_ty, hyp_body_ty);
    let stmt_for_f = d.arrow(hyp_ty, false_const);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // `source_pred_outer` must match `declare_cantor_diagonal`'s own `pred`
    // exactly (same argument order), since the proof below instantiates
    // `cantor_diagonal` at `f` and eliminates that Exists directly.
    let source_pred_outer = {
        let g0_fv = d.fresh_fvar();
        let g0 = d.kernel().fvar(g0_fv);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let g0n = d.apply(g0, &[n]);
            let fnn = d.apply(f, &[n, n]);
            let eq_ty = d.bool_eq(g0n, fnn);
            let neg_ty = d.arrow(eq_ty, false_const);
            d.pi_fv(n_fv, nat, neg_ty)
        };
        d.lam_fv(g0_fv, row_ty, body)
    };

    // cd_f : ∃ g0 : Nat -> Bool, ∀ n, Eq Bool (g0 n) (f n n) -> False
    let cd_const = d.kernel().const_(p.cantor_diagonal, vec![]);
    let cd_f = d.apply(cd_const, &[f]);

    // motive_outer := fun (_ : Exists (Nat -> Bool) source_pred_outer) => False
    let motive_outer = {
        let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
        let outer_ex_ty = d.apply(exists_c, &[row_ty, source_pred_outer]);
        let dummy_fv = d.fresh_fvar();
        d.lam_fv(dummy_fv, outer_ex_ty, false_const)
    };

    // minor_outer := fun (g0 : Nat -> Bool) (hg0 : ∀ n, Eq Bool (g0 n) (f n n) -> False) => <False>
    let minor_outer = {
        let g0_fv = d.fresh_fvar();
        let g0 = d.kernel().fvar(g0_fv);
        let hg0_ty = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let g0n = d.apply(g0, &[n]);
            let fnn = d.apply(f, &[n, n]);
            let eq_ty = d.bool_eq(g0n, fnn);
            let neg_ty = d.arrow(eq_ty, false_const);
            d.pi_fv(n_fv, nat, neg_ty)
        };
        let hg0_fv = d.fresh_fvar();
        let hg0 = d.kernel().fvar(hg0_fv);

        // ex2 : ∃ n, ∀ k, Eq Bool (f n k) (g0 k)
        let ex2 = d.apply(h, &[g0]);

        let inner_pred_g0 = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let fnk = d.apply(f, &[n, k]);
                let g0k = d.apply(g0, &[k]);
                let eq_ty = d.bool_eq(fnk, g0k);
                d.pi_fv(k_fv, nat, eq_ty)
            };
            d.lam_fv(n_fv, nat, body)
        };

        // motive_inner := fun (_ : Exists Nat inner_pred_g0) => False
        let motive_inner = {
            let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
            let inner_ex_ty = d.apply(exists_c, &[nat, inner_pred_g0]);
            let dummy2_fv = d.fresh_fvar();
            d.lam_fv(dummy2_fv, inner_ex_ty, false_const)
        };

        // minor_inner := fun (n0 : Nat) (hn0 : ∀ k, Eq Bool (f n0 k) (g0 k)) => <False>
        let minor_inner = {
            let n0_fv = d.fresh_fvar();
            let n0 = d.kernel().fvar(n0_fv);
            let hn0_ty = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let fn0k = d.apply(f, &[n0, k]);
                let g0k = d.apply(g0, &[k]);
                let eq_ty = d.bool_eq(fn0k, g0k);
                d.pi_fv(k_fv, nat, eq_ty)
            };
            let hn0_fv = d.fresh_fvar();
            let hn0 = d.kernel().fvar(hn0_fv);

            // e : Eq Bool (f n0 n0) (g0 n0), by specializing hn0 at k := n0.
            let e = d.apply(hn0, &[n0]);
            let fn0n0 = d.apply(f, &[n0, n0]);
            let g0n0 = d.apply(g0, &[n0]);
            // e_sym : Eq Bool (g0 n0) (f n0 n0) -- the order `hg0` needs.
            let e_sym = d.bool_symm(fn0n0, g0n0, e);
            let hg0_n0 = d.apply(hg0, &[n0]);
            let result = d.apply(hg0_n0, &[e_sym]);

            let with_hn0 = d.lam_fv(hn0_fv, hn0_ty, result);
            d.lam_fv(n0_fv, nat, with_hn0)
        };

        let exists_rec_inner = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let inner_result = d.apply(
            exists_rec_inner,
            &[nat, inner_pred_g0, motive_inner, minor_inner, ex2],
        );

        let with_hg0 = d.lam_fv(hg0_fv, hg0_ty, inner_result);
        d.lam_fv(g0_fv, row_ty, with_hg0)
    };

    let exists_rec_outer = d.kernel().const_(p.logic.exists_rec, vec![one]);
    let false_proof = d.apply(
        exists_rec_outer,
        &[row_ty, source_pred_outer, motive_outer, minor_outer, cd_f],
    );

    let with_h = d.lam_fv(h_fv, hyp_ty, false_proof);

    let ty = d.pi_fv(f_fv, fn2_ty, stmt_for_f);
    let value = d.lam_fv(f_fv, fn2_ty, with_h);

    d.declare_theorem(p.cantor_diagonal_neg, ty, value)
}

/// `Nat.cantor_no_fixed_point : ∀ F : Bool → Bool,
///   (∀ b, Eq Bool (F b) b → False) → (∃ d, Eq Bool (F d) d) → False`
///
/// The fixed-point corollary: a `Bool → Bool` function that disagrees with
/// every input everywhere has no fixed point. This is nearly free of the
/// case-split machinery the two theorems above needed — it is a single
/// `Exists.rec` on the fixed-point hypothesis, applying the pointwise
/// disagreement hypothesis directly at the witness — and it is the seed of
/// the halting argument's shape: a procedure that decides a self-referential
/// question by disagreeing with itself at every point cannot be applied to
/// itself.
///
/// Instantiating `F` at the diagonal's own `not` and the hypothesis at
/// [`cantor_pointwise`] (universally closed) gives "negation has no fixed
/// point on `Bool`" — checked in `nat_prelude_tests.rs`.
pub(super) fn declare_cantor_no_fixed_point(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let bool_ty = d.bool_ty();
    let false_const = d.kernel().const_(p.logic.false_, vec![]);
    let one = d.level_one();

    let fb_ty = d.arrow(bool_ty, bool_ty); // Bool -> Bool

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    // no_ne_hyp_ty := ∀ b, Eq Bool (F b) b -> False
    let (b_fv, no_ne_body_ty) = {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let fb = d.apply(f, &[b]);
        let eq_ty = d.bool_eq(fb, b);
        let neg_ty = d.arrow(eq_ty, false_const);
        (b_fv, neg_ty)
    };
    let no_ne_hyp_ty = d.pi_fv(b_fv, bool_ty, no_ne_body_ty);

    // fixed_pred := fun d => Eq Bool (F d) d
    let fixed_pred = {
        let d_fv = d.fresh_fvar();
        let dv = d.kernel().fvar(d_fv);
        let fd = d.apply(f, &[dv]);
        let eq_ty = d.bool_eq(fd, dv);
        d.lam_fv(d_fv, bool_ty, eq_ty)
    };
    let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
    let fixed_ex_ty = d.apply(exists_c, &[bool_ty, fixed_pred]);

    let stmt_for_f = {
        let inner = d.arrow(fixed_ex_ty, false_const);
        d.arrow(no_ne_hyp_ty, inner)
    };

    let no_ne_fv = d.fresh_fvar();
    let no_ne = d.kernel().fvar(no_ne_fv);
    let ex_fv = d.fresh_fvar();
    let ex = d.kernel().fvar(ex_fv);

    // motive := fun (_ : Exists Bool fixed_pred) => False
    let motive = {
        let dummy_fv = d.fresh_fvar();
        d.lam_fv(dummy_fv, fixed_ex_ty, false_const)
    };
    // minor := fun (d0 : Bool) (hd0 : Eq Bool (F d0) d0) => no_ne d0 hd0
    let minor = {
        let d0_fv = d.fresh_fvar();
        let d0 = d.kernel().fvar(d0_fv);
        let fd0 = d.apply(f, &[d0]);
        let hd0_ty = d.bool_eq(fd0, d0);
        let hd0_fv = d.fresh_fvar();
        let hd0 = d.kernel().fvar(hd0_fv);
        let no_ne_d0 = d.apply(no_ne, &[d0]);
        let result = d.apply(no_ne_d0, &[hd0]);
        let with_hd0 = d.lam_fv(hd0_fv, hd0_ty, result);
        d.lam_fv(d0_fv, bool_ty, with_hd0)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    let false_proof = d.apply(exists_rec, &[bool_ty, fixed_pred, motive, minor, ex]);

    let with_ex = d.lam_fv(ex_fv, fixed_ex_ty, false_proof);
    let with_no_ne = d.lam_fv(no_ne_fv, no_ne_hyp_ty, with_ex);

    let ty = d.pi_fv(f_fv, fb_ty, stmt_for_f);
    let value = d.lam_fv(f_fv, fb_ty, with_no_ne);

    d.declare_theorem(p.cantor_no_fixed_point, ty, value)
}

/// Declare this module's results, in dependency order: the headline theorem,
/// the negative form built on top of it, then the fixed-point corollary
/// (independent of both, but placed alongside them thematically).
pub(super) fn declare_cantor_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_cantor_diagonal(d, p)?;
    declare_cantor_diagonal_neg(d, p)?;
    declare_cantor_no_fixed_point(d, p)?;
    Ok(())
}
