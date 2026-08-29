//! `Nat.bitwise` — the general two-argument bit-combinator `land`, `lor`, and
//! `ldiff` (`land.rs`, `lor.rs`, `ldiff.rs`) were each landed **instead of**,
//! by the same structural fuel-recursion device those three files establish.
//!
//! Mathlib v4.30 (`Mathlib.Data.Nat.Bitwise`) defines
//!
//! ```text
//! def bitwise (f : Bool → Bool → Bool) : Nat → Nat → Nat
//!   | 0,     n     => if f false true  then n else 0
//!   | m + 1, 0     => if f true  false then m + 1 else 0
//!   | m + 1, n + 1 => bit (f (bodd (m+1)) (bodd (n+1)))
//!                         (bitwise f (div2 (m+1)) (div2 (n+1)))
//! ```
//!
//! `land.rs`'s module doc declined this, citing "a `Bool → Bool → Bool`
//! function threaded through mismatched-length base cases" as substantially
//! more construction than one lane's scope. **Now that all three
//! specializations exist, the actual cost of that threading is small and
//! precisely characterizable — this file lands it.**
//!
//! # What the "mismatched-length base cases" actually cost
//!
//! `land`/`lor`/`ldiff` each pick their fuel-exhaustion row (and their inner
//! `m = 0` guard) as a **fixed constant** (`0` or the current `n`), because
//! for a *specific* `f` that constant is decidable in advance: `land`'s `f`
//! is absorbing at `0` on this operand, `lor`'s is not, so the module docs
//! for each derive one closed-form row. For a *general* `f`, that same
//! question — "does the fuel operand carry this operator's absorbing
//! zero?" — has no fixed answer; it depends on `f`. Mathlib's own base cases
//! answer it the only way a general `f` allows: **evaluate `f` at the two
//! boundary `Bool` literals and branch on the result** — `f false true` for
//! the `m = 0` row, `f true false` for the `n = 0` row. Those are two
//! genuinely different partial applications of `f` (hence "mismatched"), but
//! each is just one more `bool_select_nat` gate, identical in shape to the
//! gates `land`/`lor`/`ldiff` already build for their own zero-guards. No
//! new combinator, no new primitive, no new height dependency: threading `f`
//! costs one extra bound variable through every closure and two additional
//! `d.apply(f, …)` calls at the boundary rows, plus one at the per-bit step
//! (see below). That is the entire "mismatched-length" cost.
//!
//! The one genuine wrinkle is the per-bit combine. `land`/`lor`/`ldiff` each
//! combine `m`'s and `n`'s current bit (`Nat` values already in `{0, 1}`, via
//! `Nat.mod _ 2`) with a **`Nat`-valued** formula (`mul`, `max` via
//! `ble`+`bool_select_nat`, a custom `if`). A general `f : Bool → Bool →
//! Bool` cannot be applied to those `Nat` bit values directly — it needs
//! `Bool` arguments. So the per-bit step here converts each bit to `Bool`
//! via `Nat.beq _ 1` (an *ad hoc* `bodd`; Mathlib's own `Nat.bodd` is not in
//! this prelude and is not needed just for this), applies `f`, and converts
//! the `Bool` result back to a `{0, 1}` `Nat` via `bool_select_nat`. Again:
//! reuses only primitives already load-bearing in `land`/`lor`/`ldiff`'s own
//! terms (`beq`, `bool_select_nat`), no new height dependency.
//!
//! ```text
//! Nat.bitwiseAux f 0        m n ≡ if f false true then n else 0
//! Nat.bitwiseAux f (succ k) m n ≡
//!   if n = 0 then (if f true false then m else 0)
//!   else if m = 0 then (if f false true then n else 0)
//!   else 2 * bitwiseAux f k (m/2) (n/2)
//!        + (if f (m%2 =? 1) (n%2 =? 1) then 1 else 0)
//! Nat.bitwise f m n := Nat.bitwiseAux f m m n
//! ```
//!
//! The guard order is UNCHANGED from `land`/`lor`/`ldiff` — `n = 0`
//! outermost — for the identical proof-cost reason (see `land.rs`).
//!
//! # The boundary lemmas hold for EVERY `f`, unconditionally
//!
//! [`bitwise_zero_left`](NatPrelude::bitwise_zero_left) (`bitwise f 0 n =
//! if f false true then n else 0`) is `refl`: fuel is `m = 0`, so the outer
//! `Nat.rec` hits `bitwiseAux`'s fuel-exhaustion row directly, which is
//! *exactly* this statement's RHS by construction — no fact about `f` is
//! needed, because both sides are the same term.
//!
//! [`bitwise_zero_right`](NatPrelude::bitwise_zero_right) (`bitwise f m 0 =
//! if f true false then m else 0`) needs induction on `m`, exactly
//! `land_zero_right`'s shape: each step is `refl` (the `n = 0` guard,
//! tested outermost with `n` the theorem's own literal `0`, collapses the
//! whole succ-step term to the `n = 0` row regardless of the fuel
//! predecessor). The **base case is the one new wrinkle**: at `m = 0`, the
//! LHS reduces to `bitwiseAux`'s fuel-exhaustion row (conditioned on
//! `f false true`) while the RHS is conditioned on `f true false` — two
//! *different*, generally non-defeq `Bool` terms for a symbolic `f`. Both
//! sides are still `0` at this point (`n` and `m` are both the literal `0`
//! here, so both `bool_select_nat` calls have **identical** `on_true`/
//! `on_false` branches, `0`/`0`), which is provable by a two-line `Bool`
//! case split on the (otherwise-uninspected) condition — [`bool_select_same`]
//! below, a general "`if c then v else v ≡ v`" lemma independent of what `c`
//! is. This is genuinely new proof content beyond `land`/`lor`/`ldiff`'s
//! zero-right theorems (which needed no such lemma, because their base cases
//! were already syntactically identical on both sides), but it is small: one
//! four-line helper, applied twice.
//!
//! Neither boundary lemma needs `f false false = false` — the hypothesis
//! Mathlib's own *correctness* lemmas (`testBit_bitwise`, etc.) carry, and
//! which this file does not attempt to reconstruct. (The universal
//! `∀ m n, bitwise f m n = <sibling> m n` equivalences, which this file
//! originally scoped out, are proved in
//! [`rec_agreement`](super::rec_agreement) — see the next section.)
//!
//! # The universal equivalence: DONE, in [`rec_agreement`](super::rec_agreement)
//!
//! **This section used to say a full `∀ m n, bitwise and m n = land m n` was
//! not attempted and was "sized past this lane's scope". That is no longer
//! true, and the text is corrected rather than deleted because the two
//! obstacles it named were the right ones.** They were:
//!
//! 1. an induction relating two independently-built `Nat.rec` instances, and
//! 2. a `Nat.mod _ 2 ∈ {0, 1}` case-split lemma the prelude did not carry.
//!
//! Both now exist in [`ops`](super::ops) — `agree_by_fuel_induction` and
//! `cases_mod_two` — and [`NatPrelude::bitwise_and_eq_land`] /
//! [`NatPrelude::bitwise_or_eq_lor`] are admitted universally, superseding
//! the concrete witnesses below.
//!
//! The diagnosis above was accurate about *where* the difficulty lives:
//! `bitwiseAux`'s per-bit step and `landAux`'s are different formulas
//! (`bool_select_nat (and (beq a 1) (beq b 1)) 1 0` vs. `mul a b`) that agree
//! at every concrete `a, b ∈ {0, 1}` and are not definitionally equal at
//! symbolic `a, b`. What it did not anticipate is that the **base cases cost
//! nothing** — evaluating a concrete `f` at the boundary `Bool` literals
//! reproduces each sibling's hand-chosen fuel-exhaustion row by δβι alone, so
//! all of `land`/`lor`/`ldiff`'s carefully-distinguished rows line up with
//! `bitwise`'s automatically. See `rec_agreement.rs`'s module doc.
//!
//! [`bitwise_and_eq_land_three_five`](NatPrelude::bitwise_and_eq_land_three_five)
//! and [`bitwise_or_eq_lor_three_five`](NatPrelude::bitwise_or_eq_lor_three_five)
//! are kept: they state `Eq (bitwise and_fn 3 5) (land 3 5)` / `… (lor 3 5)`
//! and close by `refl` at operands where `land`/`lor`'s own sanity checks
//! already discriminate a wrong-way step, so they remain a *reduction*-based
//! check that is independent of the induction above.
//! [`bitwise_xor_three_five`](NatPrelude::bitwise_xor_three_five) has no
//! universal counterpart, because this prelude declares no `Nat.xor` sibling
//! to agree with — Mathlib defines `Nat.xor := bitwise xor` at the pinned
//! commit, so the general form is the only definition on offer either way.

use super::NatPrelude;
use super::bit_decode::case_bool;
use super::ops::{
    NatDev, NatOps, agree_by_double_fuel_induction, agree_by_fuel_induction, bool_select_nat_same,
    cases_zero_succ, two_mul_eq_add_self,
};
use super::rec_agreement::half_le_predecessor_of_succ;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

/// `Nat.bitwiseAux f fuel m n`.
fn bitwise_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    fuel: ExprId,
    m: ExprId,
    n: ExprId,
) -> ExprId {
    d.const_app(p.bitwise_aux, &[f, fuel, m, n])
}

/// `Nat.bitwise f m n`.
fn bitwise(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, m: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.bitwise, &[f, m, n])
}

/// `Bool.rec` at a `Bool`-valued motive: computational `if condition then
/// on_true else on_false` at `Bool`, the `Bool`-codomain twin of
/// [`NatOps::bool_select_nat`]. Not in `ops.rs` because no other file in
/// this prelude needs a `Bool`-valued `if` — `land`/`lor`/`ldiff` only ever
/// select `Nat` values. Generic over `D: NatOps` (not the concrete
/// [`NatDev`] every other helper in this file uses) so the test suite's own
/// `Fixture` can build the same `and`/`or`/`xor` terms it checks against.
fn bool_select_bool<D: NatOps>(
    d: &mut D,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.prelude().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `fun a b => bool_select_bool a b false` — `Bool.and`, built inline (this
/// prelude declares no top-level `Bool.and`) purely to instantiate
/// `bitwise`'s `f` slot for the evaluation tests below. Generic for the
/// same reason as [`bool_select_bool`].
pub(super) fn and_fn<D: NatOps>(d: &mut D) -> ExprId {
    let bool_ty = d.bool_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let false_ = d.bool_false();
    let body = bool_select_bool(d, a, b, false_);
    let with_b = d.lam_fv(b_fv, bool_ty, body);
    d.lam_fv(a_fv, bool_ty, with_b)
}

/// `fun a b => bool_select_bool a true b` — `Bool.or`, built inline for the
/// same reason as [`and_fn`].
pub(super) fn or_fn<D: NatOps>(d: &mut D) -> ExprId {
    let bool_ty = d.bool_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let true_ = d.bool_true();
    let body = bool_select_bool(d, a, true_, b);
    let with_b = d.lam_fv(b_fv, bool_ty, body);
    d.lam_fv(a_fv, bool_ty, with_b)
}

/// `fun a b => bool_select_bool a (bool_select_bool b false true) b` —
/// `Bool.xor` (`if a then not b else b`), built inline for the same reason
/// as [`and_fn`]. Neither `land` nor `lor` has an XOR sibling to cross-check
/// against, so [`declare_bitwise_all`] checks this one only against a
/// hand-computed numeral (`3 xor 5 = 6`), not against an existing prelude
/// declaration.
pub(super) fn xor_fn<D: NatOps>(d: &mut D) -> ExprId {
    let bool_ty = d.bool_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let not_b = bool_select_bool(d, b, false_, true_);
    let body = bool_select_bool(d, a, not_b, b);
    let with_b = d.lam_fv(b_fv, bool_ty, body);
    d.lam_fv(a_fv, bool_ty, with_b)
}

/// `fun a b => a` — the first-projection function, deliberately
/// **non-commutative** (`fst true false = true`, `fst false true = false`,
/// so `fst a b != fst b a` in general). `and`/`or`/`xor` are all
/// commutative, so NONE of them can discriminate [`declare_bitwise_swap`]'s
/// statement from the vacuous case where swapping `f`'s arguments changes
/// nothing — this is the test-only fixture that actually exercises the
/// swap (`swap fst = fun a b => b`, the second projection). `#[cfg(test)]`
/// because it has no production consumer — unlike `and_fn`/`or_fn`/`xor_fn`,
/// which [`declare_bitwise_all`]'s own `_three_five` checks also use, this
/// exists solely for `nat_prelude_tests`'s discriminating instance.
#[cfg(test)]
pub(super) fn fst_fn<D: NatOps>(d: &mut D) -> ExprId {
    let bool_ty = d.bool_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let with_b = d.lam_fv(b_fv, bool_ty, a);
    d.lam_fv(a_fv, bool_ty, with_b)
}

/// `∀ (v : Nat) (x : Bool), Eq (bool_select_nat x v v) v` — "both branches
/// of this `if` are the same value, so the value is `v` regardless of the
/// (possibly symbolic, unevaluated) condition". Proved by a plain `Bool`
/// case split on `x`; both cases are `refl` because `bool_select_nat`'s two
/// branches are syntactically `v` here. The one piece of proof content
/// `bitwise_zero_right`'s base case needs that `land`/`lor`/`ldiff`'s
/// zero-right theorems never did — see the module doc.
fn bool_select_same(d: &mut NatDev<'_>, v: ExprId, x: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let motive = {
        let val_fv = d.fresh_fvar();
        let val = d.kernel().fvar(val_fv);
        let lhs = d.bool_select_nat(val, v, v);
        let stmt = d.eq(lhs, v);
        d.lam_fv(val_fv, bool_ty, stmt)
    };
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let case_false = {
        let lhs = d.bool_select_nat(false_, v, v);
        d.refl(lhs)
    };
    let case_true = {
        let lhs = d.bool_select_nat(true_, v, v);
        d.refl(lhs)
    };
    let z = d.kernel().level_zero();
    let bool_rec = d.prelude().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![z]);
    d.apply(rec, &[motive, case_false, case_true, x])
}

/// Declare `theorem name : ∀ (f : Bool → Bool → Bool) (x_0 … : Nat), stmt :=
/// …`, the `f`-quantified twin of [`NatOps::theorem`] (which only ever
/// quantifies over `Nat`). `build` receives the bound `f` and the `nat_arity`
/// bound `Nat` variables and returns `(statement, proof)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn theorem_with_f(
    d: &mut NatDev<'_>,
    name: NameId,
    nat_arity: usize,
    build: &dyn Fn(&mut NatDev<'_>, ExprId, &[ExprId]) -> (ExprId, ExprId),
) -> Result<ExprId, KernelError> {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let f_ty = {
        let inner = d.arrow(bool_ty, bool_ty);
        d.arrow(bool_ty, inner)
    };
    let f_fv = d.fresh_fvar();
    let f_expr = d.kernel().fvar(f_fv);
    let fvs: Vec<u64> = (0..nat_arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
    let (stmt, proof) = build(d, f_expr, &vars);
    let mut ty = stmt;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, nat, ty);
        value = d.lam_fv(fv, nat, value);
    }
    ty = d.pi_fv(f_fv, f_ty, ty);
    value = d.lam_fv(f_fv, f_ty, value);
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(ty)
}

/// Declare `Nat.bitwiseAux`, `Nat.bitwise`, two `f`-general boundary
/// theorems, and three concrete specialization checks.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_bitwise_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);
    // The Nat.rec row type once the fuel argument has been consumed: a
    // function of the two remaining arguments `m` and `n`.
    let row_ty = d.arrow(nat, nat_to_nat);
    let f_ty = {
        let inner = d.arrow(bool_ty, bool_ty);
        d.arrow(bool_ty, inner)
    };

    // --- Nat.bitwiseAux : (Bool -> Bool -> Bool) -> Nat -> Nat -> Nat -> Nat -
    {
        let f_fv = d.fresh_fvar();
        let f_expr = d.kernel().fvar(f_fv);

        // fuel = zero: `if f false true then n else 0`, ignoring `m` -- see
        // the module doc: `m` is both the fuel and (by the halving
        // invariant `land`/`lor`/`ldiff` establish) definitionally `0` by
        // the time fuel is exhausted, matching Mathlib's `(0, n)` case.
        let zero_minor = {
            let m_fv = d.fresh_fvar();
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let false_ = d.bool_false();
            let true_ = d.bool_true();
            let cond = d.apply(f_expr, &[false_, true_]);
            let zero = d.zero();
            let body = d.bool_select_nat(cond, n, zero);
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(m_fv, nat, with_n)
        };

        // fuel = succ predecessor: guard on `n = 0` OUTERMOST (returning
        // `if f true false then m else 0`, Mathlib's `(m+1, 0)` shortcut),
        // then `m = 0` (returning `if f false true then n else 0`, the same
        // formula as `zero_minor`) -- see the module doc for why the order
        // is load-bearing. The real bitwise-at-this-bit step converts each
        // operand's current bit to `Bool` via `beq _ 1`, applies `f`, and
        // converts back via `bool_select_nat`.
        let succ_minor = {
            let predecessor_fv = d.fresh_fvar();
            let row_fv = d.fresh_fvar();
            let row = d.kernel().fvar(row_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);

            let zero = d.zero();
            let two = d.num(2);
            let one_nat = d.num(1);
            let true_ = d.bool_true();
            let false_ = d.bool_false();

            let half_m = d.div(m, two);
            let half_n = d.div(n, two);
            let recursive = d.apply(row, &[half_m, half_n]);
            let doubled = d.mul(two, recursive);

            let bit_m = d.modulo(m, two);
            let bit_n = d.modulo(n, two);
            let bit_m_bool = d.beq(bit_m, one_nat);
            let bit_n_bool = d.beq(bit_n, one_nat);
            let combined_bool = d.apply(f_expr, &[bit_m_bool, bit_n_bool]);
            let combined_nat = d.bool_select_nat(combined_bool, one_nat, zero);
            let stepped = d.add(doubled, combined_nat);

            let f_true_false = d.apply(f_expr, &[true_, false_]);
            let n_zero_branch = d.bool_select_nat(f_true_false, m, zero);

            let f_false_true = d.apply(f_expr, &[false_, true_]);
            let m_zero_branch = d.bool_select_nat(f_false_true, n, zero);

            let m_is_zero = d.beq(m, zero);
            let inner = d.bool_select_nat(m_is_zero, m_zero_branch, stepped);
            let n_is_zero = d.beq(n, zero);
            let body = d.bool_select_nat(n_is_zero, n_zero_branch, inner);

            let with_n = d.lam_fv(n_fv, nat, body);
            let with_m = d.lam_fv(m_fv, nat, with_n);
            let with_row = d.lam_fv(row_fv, row_ty, with_m);
            d.lam_fv(predecessor_fv, nat, with_row)
        };

        let motive = d.kernel().lam(anon, nat, row_ty, BinderInfo::Default);
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let row = d.apply(rec, &[motive, zero_minor, succ_minor, fuel]);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let applied = d.apply(row, &[m, n]);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, applied);
            let with_m = d.lam_fv(m_fv, nat, with_n);
            let with_fuel = d.lam_fv(fuel_fv, nat, with_m);
            d.lam_fv(f_fv, f_ty, with_fuel)
        };
        let ty = {
            let fuel_ty = d.arrow(nat, row_ty);
            d.arrow(f_ty, fuel_ty)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.bitwise_aux,
            uparams: vec![],
            // Strictly greater than the height of everything it calls
            // (`Nat.div`/`Nat.mod` are height 3, `Nat.mul`/`Nat.beq` are
            // lower still) -- matches `landAux`/`lorAux`/`ldiffAux`'s choice
            // for the identical call-graph shape; `bool_select_nat`/
            // `Bool.rec` applications are inline, not named definitions, so
            // they add no height dependency.
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.bitwise f m n := Nat.bitwiseAux f m m n ------------------------
    {
        let f_fv = d.fresh_fvar();
        let f_expr = d.kernel().fvar(f_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = bitwise_aux(d, &p, f_expr, m, m, n);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            let with_m = d.lam_fv(m_fv, nat, with_n);
            d.lam_fv(f_fv, f_ty, with_m)
        };
        let ty = {
            let inner = d.arrow(nat, nat_to_nat);
            d.arrow(f_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.bitwise,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // bitwise_zero_left : ∀ f n, Eq (bitwise f 0 n) (if f false true then n
    // else 0) -- refl: fuel = m = 0 exhausts the outer Nat.rec immediately,
    // hitting `bitwiseAux`'s fuel-exhaustion row, which IS this RHS by
    // construction. Holds for every `f`, no hypothesis needed.
    theorem_with_f(d, p.bitwise_zero_left, 1, &|d, f_expr, values| {
        let n = values[0];
        let zero = d.zero();
        let false_ = d.bool_false();
        let true_ = d.bool_true();
        let cond = d.apply(f_expr, &[false_, true_]);
        let rhs = d.bool_select_nat(cond, n, zero);
        let lhs = bitwise(d, &p, f_expr, zero, n);
        (d.eq(lhs, rhs), d.refl(lhs))
    })?;

    // bitwise_zero_right : ∀ f m, Eq (bitwise f m 0) (if f true false then m
    // else 0) -- induction on m; each step is refl (the n = 0 guard, tested
    // outermost with the theorem's own literal 0, collapses immediately,
    // exactly `land_zero_right`'s shape). The base case needs
    // `bool_select_same` -- see the module doc.
    theorem_with_f(d, p.bitwise_zero_right, 1, &|d, f_expr, values| {
        let m = values[0];
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let f_true_false = d.apply(f_expr, &[true_, false_]);
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| {
            let zero = d.zero();
            let lhs = bitwise(d, &p, f_expr, candidate, zero);
            let rhs = d.bool_select_nat(f_true_false, candidate, zero);
            d.eq(lhs, rhs)
        };
        let proof = d.induct(
            &statement_at,
            &|d| {
                let zero = d.zero();
                let true_ = d.bool_true();
                let false_ = d.bool_false();
                let f_true_false = d.apply(f_expr, &[true_, false_]);
                let f_false_true = d.apply(f_expr, &[false_, true_]);
                // LHS = bitwise f 0 0, defeq bool_select_nat f_false_true 0 0.
                let lhs_reduced = d.bool_select_nat(f_false_true, zero, zero);
                let lhs_eq_zero = bool_select_same(d, zero, f_false_true);
                // RHS (the statement's own RHS at m = 0) =
                // bool_select_nat f_true_false 0 0.
                let rhs_reduced = d.bool_select_nat(f_true_false, zero, zero);
                let rhs_eq_zero = bool_select_same(d, zero, f_true_false);
                let zero_eq_rhs = d.symm(rhs_reduced, zero, rhs_eq_zero);
                d.trans(lhs_reduced, zero, rhs_reduced, lhs_eq_zero, zero_eq_rhs)
            },
            &|d, predecessor, _ih| {
                let candidate = d.succ(predecessor);
                let zero = d.zero();
                let lhs = bitwise(d, &p, f_expr, candidate, zero);
                d.refl(lhs)
            },
            m,
        );
        let stmt = statement_at(d, m);
        (stmt, proof)
    })?;

    // --- Concrete specialization checks -------------------------------------
    //
    // No universal `∀ m n, bitwise and m n = land m n` proof was attempted
    // (see the module doc); these are the strongest available check without
    // it -- both sides fully compute to the same literal numeral.

    // bitwise_and_eq_land_three_five : Eq (bitwise and_fn 3 5) (land 3 5)
    // -- both sides reduce to 1 (0b011 & 0b101 = 0b001).
    {
        let and_ = and_fn(d);
        let three = d.num(3);
        let five = d.num(5);
        let lhs = bitwise(d, &p, and_, three, five);
        let rhs = d.const_app(p.land, &[three, five]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.bitwise_and_eq_land_three_five,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })?;
    }

    // bitwise_or_eq_lor_three_five : Eq (bitwise or_fn 3 5) (lor 3 5) --
    // both sides reduce to 7 (0b011 | 0b101 = 0b111).
    {
        let or_ = or_fn(d);
        let three = d.num(3);
        let five = d.num(5);
        let lhs = bitwise(d, &p, or_, three, five);
        let rhs = d.const_app(p.lor, &[three, five]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.bitwise_or_eq_lor_three_five,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })?;
    }

    // bitwise_xor_three_five : Eq (bitwise xor_fn 3 5) 6 -- 0b011 xor 0b101
    // = 0b110. No prelude XOR sibling exists to cross-check against, so
    // this closes against a hand-computed numeral instead.
    {
        let xor_ = xor_fn(d);
        let three = d.num(3);
        let five = d.num(5);
        let six = d.num(6);
        let lhs = bitwise(d, &p, xor_, three, five);
        let stmt = d.eq(lhs, six);
        let proof = d.refl(lhs);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.bitwise_xor_three_five,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })?;
    }

    Ok(())
}

// ============================================================================
// `Nat.bitwise_comm` — commutativity of the general combinator, for a
// SYMBOLIC `f` known only to be commutative (`hf : ∀ a b, f a b = f b a`).
//
// A Python simulation (recorded in
// `docs/plan/status/256-nat-bitwise-comm.md`) confirmed the prediction this
// module's own agreement work implies: the UNCONDITIONAL form
// `bitwiseAux f fuel m n = bitwiseAux f fuel n m` is FALSE when `fuel` is
// insufficient and `f false true = true` (`f = or`, `f = xor`) — e.g.
// `bitwiseAux(or, 0, 0, 1) = 1` but `bitwiseAux(or, 0, 1, 0) = 0` — and true
// only when `f false true = false` (`f = and`, matching `land`'s own
// absorbing-zero row). So this needs `lor`'s shape, `Le m fuel → Le n fuel →
// …`, not `land`'s unconditional one, PLUS an explicit `hf` hypothesis
// `land`/`lor` never needed (their `f` is fixed and concrete).
//
// `hf` earns its keep in TWO places, not one: the per-bit combine (as
// expected — `bitwise_bit_comm` below), and ALSO the `m = 0`/`n = 0`
// boundary. For a concrete `f`, `land`/`lor`'s boundary rows evaluate to the
// SAME literal on both sides trivially; here the two boundary rows are
// `f false true`- and `f true false`-conditioned respectively, two
// DIFFERENT partial applications of a symbolic `f` that are equal only
// because `hf` says so (`hf true false`). This is genuinely new proof
// content beyond `lor_aux_comm_of_fuel`'s transport.
// ============================================================================

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)` — the `Bool`-scrutinee, `Nat`-
/// conclusion twin of [`NatOps::congr`] (whose `eq_motive`/`transport` are
/// hardcoded to `Nat` throughout, so `congr` itself cannot express a
/// hypothesis about a `Bool` equality). Built from `ops.rs`'s ALREADY
/// GENERIC [`NatOps::bool_eq_motive`]/[`NatOps::bool_transport`] — a first
/// pass at this file duplicated `Eq.{1} Bool` and the raw `Eq.rec`
/// application by hand before noticing `ops.rs` already carries the whole
/// `bool_eq`/`bool_refl`/`bool_transport`/`bool_eq_motive` family (built for
/// `false_true_elim`), exactly the "search for the STEP, not the NAME" trap
/// this project's own notes warn about.
fn congr_bool_to_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `guarded`'s shape from `rec_agreement.rs` (private there): the common
/// `bitwiseAux (succ k) m n ≡ if n = 0 then on_n_zero else if m = 0 then
/// on_m_zero else 2 * recursive + bit` skeleton, matching what
/// [`declare_bitwise_all`]'s `succ_minor` builds inline. Duplicated
/// (5 lines) rather than widening `rec_agreement.rs`'s visibility for a
/// shape this file already constructs by hand once.
fn guarded(
    d: &mut NatDev<'_>,
    m: ExprId,
    n: ExprId,
    on_n_zero: ExprId,
    on_m_zero: ExprId,
    recursive: ExprId,
    bit: ExprId,
) -> ExprId {
    let two = d.num(2);
    let zero = d.zero();
    let doubled = d.mul(two, recursive);
    let stepped = d.add(doubled, bit);
    let m_is_zero = d.beq(m, zero);
    let inner = d.bool_select_nat(m_is_zero, on_m_zero, stepped);
    let n_is_zero = d.beq(n, zero);
    d.bool_select_nat(n_is_zero, on_n_zero, inner)
}

/// `Eq (bool_select_nat (f (beq (m%2) 1) (beq (n%2) 1)) 1 0) (bool_select_nat
/// (f (beq (n%2) 1) (beq (m%2) 1)) 1 0)` — the per-bit step swaps under `f`
/// DIRECTLY via `hf (beq (m%2) 1) (beq (n%2) 1)` (no case split needed,
/// unlike [`bit_agreement`]: `hf` already IS the equality at these two
/// concrete-shaped-but-symbolic-valued `Bool` terms), then lifts that
/// `Bool` equality through `bool_select_nat`'s condition slot via
/// [`congr_bool_to_nat`].
fn bitwise_bit_comm(
    d: &mut NatDev<'_>,
    f_expr: ExprId,
    hf_expr: ExprId,
    m: ExprId,
    n: ExprId,
) -> ExprId {
    let two = d.num(2);
    let one = d.num(1);
    let bit_m = d.modulo(m, two);
    let bit_n = d.modulo(n, two);
    let bit_m_bool = d.beq(bit_m, one);
    let bit_n_bool = d.beq(bit_n, one);
    let combined = d.apply(f_expr, &[bit_m_bool, bit_n_bool]);
    let combined_swapped = d.apply(f_expr, &[bit_n_bool, bit_m_bool]);
    let h = d.apply(hf_expr, &[bit_m_bool, bit_n_bool]);
    congr_bool_to_nat(d, combined, combined_swapped, h, &|d, cond| {
        let one = d.num(1);
        let zero = d.zero();
        d.bool_select_nat(cond, one, zero)
    })
}

/// `bitwise_aux_zero_left_any_fuel : ∀ f fuel n, Eq (bitwiseAux f fuel 0 n)
/// (bool_select_nat (f false true) n 0)` — unconditional in `f`, the
/// `bitwise` twin of [`super::rec_agreement`]'s `…_zero_left_any_fuel`
/// family. `fuel = 0` is `refl` (the base row ignores `m`); `fuel = succ f`
/// needs `n`'s own shape exposed (`lor`'s wrinkle, not `land`'s — see
/// `rec_agreement.rs`'s module doc), and at `n = 0` the two guard branches
/// (`f true false`- and `f false true`-conditioned, both applied to the
/// literal `0`) are related by [`bool_select_same`] independently rather
/// than by `hf` — no commutativity hypothesis is needed here, because BOTH
/// sides are being shown equal to `0`, not to each other via a swap.
fn declare_bitwise_aux_zero_left_any_fuel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    theorem_with_f(
        d,
        p.bitwise_aux_zero_left_any_fuel,
        2,
        &|d, f_expr, values| {
            let fuel = values[0];
            let n = values[1];
            let zero = d.zero();
            let false_ = d.bool_false();
            let true_ = d.bool_true();
            let f_false_true = d.apply(f_expr, &[false_, true_]);

            let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
                let lhs = bitwise_aux(d, &p, f_expr, candidate, zero, n);
                let rhs = d.bool_select_nat(f_false_true, n, zero);
                d.eq(lhs, rhs)
            };

            let proof = cases_zero_succ(
                d,
                fuel,
                &statement_at,
                &|d| {
                    let lhs = bitwise_aux(d, &p, f_expr, zero, zero, n);
                    d.refl(lhs)
                },
                &|d, predecessor| {
                    let succ_pred = d.succ(predecessor);
                    let n_goal = |d: &mut NatDev<'_>, candidate_n: ExprId| -> ExprId {
                        let lhs = bitwise_aux(d, &p, f_expr, succ_pred, zero, candidate_n);
                        let rhs = d.bool_select_nat(f_false_true, candidate_n, zero);
                        d.eq(lhs, rhs)
                    };
                    cases_zero_succ(
                        d,
                        n,
                        &n_goal,
                        &|d| {
                            let true_ = d.bool_true();
                            let false_ = d.bool_false();
                            let f_true_false = d.apply(f_expr, &[true_, false_]);
                            let lhs = bitwise_aux(d, &p, f_expr, succ_pred, zero, zero);
                            let target = d.bool_select_nat(f_false_true, zero, zero);
                            let lhs_is_zero = bool_select_same(d, zero, f_true_false);
                            let target_is_zero = bool_select_same(d, zero, f_false_true);
                            let target_is_zero_rev = d.symm(target, zero, target_is_zero);
                            d.trans(lhs, zero, target, lhs_is_zero, target_is_zero_rev)
                        },
                        &|d, n_pred| {
                            let succ_n_pred = d.succ(n_pred);
                            let lhs = bitwise_aux(d, &p, f_expr, succ_pred, zero, succ_n_pred);
                            d.refl(lhs)
                        },
                    )
                },
            );
            let stmt = statement_at(d, fuel);
            (stmt, proof)
        },
    )?;
    Ok(())
}

/// `bitwise_aux_agree_of_fuel : ∀ f fuel1 m n fuel2, Le m fuel1 → Le m fuel2
/// → Eq (bitwiseAux f fuel1 m n) (bitwiseAux f fuel2 m n)` — two
/// independently-chosen sufficient fuels agree, the `bitwise` twin of
/// [`super::rec_agreement`]'s `land`/`lor` `…_agree_of_fuel` lemmas
/// ([`agree_by_double_fuel_induction`]). No `hf` hypothesis: fuel-irrelevance
/// never swaps the two value arguments, so it holds for EVERY `f`, not just
/// commutative ones. The `m = succ predecessor` step's guard values are
/// `bitwiseAux`'s REAL formulas (`bool_select_nat (f true false) …`/
/// `bool_select_nat (f false true) …`), not placeholders — unlike
/// [`declare_bitwise_aux_comm_of_fuel`]'s both-nonzero branch, `n` here
/// stays symbolic, so the guard never reduces and the placeholder trick
/// (any well-typed value discarded by a REDUCED `false` condition) does not
/// apply.
fn declare_bitwise_aux_agree_of_fuel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let f_ty = {
        let inner = d.arrow(bool_ty, bool_ty);
        d.arrow(bool_ty, inner)
    };

    let f_fv = d.fresh_fvar();
    let f_expr = d.kernel().fvar(f_fv);
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let f_false_true = d.apply(f_expr, &[false_, true_]);
    let f_true_false = d.apply(f_expr, &[true_, false_]);

    let statement = |d: &mut NatDev<'_>, fuel1: ExprId, m: ExprId, n: ExprId, fuel2: ExprId| {
        let bound1 = d.le(m, fuel1);
        let bound2 = d.le(m, fuel2);
        let lhs = bitwise_aux(d, &p, f_expr, fuel1, m, n);
        let rhs = bitwise_aux(d, &p, f_expr, fuel2, m, n);
        let concl = d.eq(lhs, rhs);
        let inner = d.arrow(bound2, concl);
        d.arrow(bound1, inner)
    };

    let base = |d: &mut NatDev<'_>, m: ExprId, n: ExprId, fuel2: ExprId| -> ExprId {
        let zero = d.zero();
        let bound1_ty = d.le(m, zero);
        let bound2_ty = d.le(m, fuel2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();

        let zero_le_m = d.lemma(p.zero_le, &[m]);
        let m_eq_zero = d.lemma(p.le_antisymm, &[m, zero, h1, zero_le_m]);

        let left_term = bitwise_aux(d, &p, f_expr, zero, m, n);
        let right_term = bitwise_aux(d, &p, f_expr, fuel2, m, n);
        let target = d.bool_select_nat(f_false_true, n, zero);
        let left_is_target = d.refl(left_term);

        let right_at_zero = bitwise_aux(d, &p, f_expr, fuel2, zero, n);
        let right_congr = d.congr(m, zero, m_eq_zero, &|d, x| {
            bitwise_aux(d, &p, f_expr, fuel2, x, n)
        });
        let any_fuel = d.lemma(p.bitwise_aux_zero_left_any_fuel, &[f_expr, fuel2, n]);
        let (_, right_is_target) = d.chain(
            right_term,
            &[(right_at_zero, right_congr), (target, any_fuel)],
        );
        let right_is_target_rev = d.symm(right_term, target, right_is_target);

        let body = d.trans(
            left_term,
            target,
            right_term,
            left_is_target,
            right_is_target_rev,
        );
        let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
        d.lam_fv(h1_fv, bound1_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>,
                k: ExprId,
                ih: ExprId,
                m: ExprId,
                n: ExprId,
                fuel2: ExprId|
     -> ExprId {
        let sk = d.succ(k);
        let goal_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound1 = d.le(candidate, sk);
            let bound2 = d.le(candidate, fuel2);
            let lhs = bitwise_aux(d, &p, f_expr, sk, candidate, n);
            let rhs = bitwise_aux(d, &p, f_expr, fuel2, candidate, n);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound2, concl);
            d.arrow(bound1, inner)
        };

        cases_zero_succ(
            d,
            m,
            &goal_at,
            &|d| {
                let zero = d.zero();
                let bound1_ty = d.le(zero, sk);
                let bound2_ty = d.le(zero, fuel2);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();

                let left_term = bitwise_aux(d, &p, f_expr, sk, zero, n);
                let right_term = bitwise_aux(d, &p, f_expr, fuel2, zero, n);
                let target = d.bool_select_nat(f_false_true, n, zero);
                let left_is_target = d.lemma(p.bitwise_aux_zero_left_any_fuel, &[f_expr, sk, n]);
                let right_is_target =
                    d.lemma(p.bitwise_aux_zero_left_any_fuel, &[f_expr, fuel2, n]);
                let right_is_target_rev = d.symm(right_term, target, right_is_target);
                let body = d.trans(
                    left_term,
                    target,
                    right_term,
                    left_is_target,
                    right_is_target_rev,
                );

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
            &|d, predecessor| {
                let succ_pred = d.succ(predecessor);
                let bound1_ty = d.le(succ_pred, sk);
                let bound2_ty = d.le(succ_pred, fuel2);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);

                let two = d.num(2);
                let half = d.div(succ_pred, two);
                let half_n = d.div(n, two);
                let one = d.num(1);
                let zero = d.zero();
                let bit_m = d.modulo(succ_pred, two);
                let bit_n = d.modulo(n, two);
                let bit_m_bool = d.beq(bit_m, one);
                let bit_n_bool = d.beq(bit_n, one);
                let combined = d.apply(f_expr, &[bit_m_bool, bit_n_bool]);
                let bit_general = d.bool_select_nat(combined, one, zero);
                let on_n_zero = d.bool_select_nat(f_true_false, succ_pred, zero);
                let on_m_zero = d.bool_select_nat(f_false_true, n, zero);

                let half_le_k = half_le_predecessor_of_succ(d, &p, predecessor, k, h1);

                let one_le_succ_pred = d.zero_lt_succ(predecessor);
                let one_le_fuel2 =
                    d.lemma(p.le_trans, &[one, succ_pred, fuel2, one_le_succ_pred, h2]);
                let succ_pred_fuel2 = d.lemma(p.succ_pred_of_pos, &[fuel2, one_le_fuel2]);
                let f2p = d.pred(fuel2);
                let succ_f2p = d.succ(f2p);
                let h2_motive = d.eq_motive(fuel2, &|d, x| d.le(succ_pred, x));
                let h2_at_succ_f2p = d.transport(fuel2, h2_motive, h2, succ_f2p, succ_pred_fuel2);
                let half_le_f2p =
                    half_le_predecessor_of_succ(d, &p, predecessor, f2p, h2_at_succ_f2p);

                let ih_at_half = d.apply(ih, &[half, half_n, f2p]);
                let ih_at_half = d.apply(ih_at_half, &[half_le_k, half_le_f2p]);

                let recursive_general = bitwise_aux(d, &p, f_expr, k, half, half_n);
                let recursive_at_f2p = bitwise_aux(d, &p, f_expr, f2p, half, half_n);

                let start = guarded(
                    d,
                    succ_pred,
                    n,
                    on_n_zero,
                    on_m_zero,
                    recursive_general,
                    bit_general,
                );
                let mid = guarded(
                    d,
                    succ_pred,
                    n,
                    on_n_zero,
                    on_m_zero,
                    recursive_at_f2p,
                    bit_general,
                );
                let inner_step = d.congr(
                    recursive_general,
                    recursive_at_f2p,
                    ih_at_half,
                    &|d, hole| guarded(d, succ_pred, n, on_n_zero, on_m_zero, hole, bit_general),
                );

                let outer_step = d.congr(fuel2, succ_f2p, succ_pred_fuel2, &|d, x| {
                    bitwise_aux(d, &p, f_expr, x, succ_pred, n)
                });
                let final_target = bitwise_aux(d, &p, f_expr, fuel2, succ_pred, n);
                let mid2 = bitwise_aux(d, &p, f_expr, succ_f2p, succ_pred, n);
                let outer_step_rev = d.symm(final_target, mid2, outer_step);

                let body = d.trans(start, mid, final_target, inner_step, outer_step_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
        )
    };

    let fuel1_fv = d.fresh_fvar();
    let fuel1 = d.kernel().fvar(fuel1_fv);
    let proof_fn = agree_by_double_fuel_induction(d, &statement, &base, &step, fuel1);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fuel2_fv = d.fresh_fvar();
    let fuel2 = d.kernel().fvar(fuel2_fv);
    let applied = d.apply(proof_fn, &[m, n, fuel2]);

    let ty_inner = {
        let body = statement(d, fuel1, m, n, fuel2);
        let with_fuel2 = d.pi_fv(fuel2_fv, nat, body);
        let with_n = d.pi_fv(n_fv, nat, with_fuel2);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(fuel1_fv, nat, with_m)
    };
    let value_inner = {
        let with_fuel2 = d.lam_fv(fuel2_fv, nat, applied);
        let with_n = d.lam_fv(n_fv, nat, with_fuel2);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(fuel1_fv, nat, with_m)
    };
    let ty = d.pi_fv(f_fv, f_ty, ty_inner);
    let value = d.lam_fv(f_fv, f_ty, value_inner);
    d.declare_theorem(p.bitwise_aux_agree_of_fuel, ty, value)
}

/// `bitwise_aux_comm_of_fuel : ∀ f, (∀ a b, Eq (f a b) (f b a)) → ∀ fuel m n,
/// Le m fuel → Le n fuel → Eq (bitwiseAux f fuel m n) (bitwiseAux f fuel n
/// m)` — commutativity of `bitwiseAux` at a SHARED fuel, `lor`'s shape (both
/// `Le` hypotheses, NOT `land`'s unconditional one — see the section doc).
/// The both-nonzero step's guard values ARE placeholders (`succ_a`,
/// `succ_b` themselves): both `beq(succ_a, 0)` and `beq(succ_b, 0)` reduce
/// to the literal `false` regardless of the guard VALUES sitting in the
/// discarded branch, exactly [`super::rec_agreement`]'s `lor_aux_comm_of_fuel`
/// precedent — unlike [`declare_bitwise_aux_agree_of_fuel`]'s step, where
/// one operand stays symbolic and the placeholder trick does not apply.
fn declare_bitwise_aux_comm_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let f_ty = {
        let inner = d.arrow(bool_ty, bool_ty);
        d.arrow(bool_ty, inner)
    };

    let f_fv = d.fresh_fvar();
    let f_expr = d.kernel().fvar(f_fv);

    let hf_ty = {
        let a_fv = d.fresh_fvar();
        let a_local = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b_local = d.kernel().fvar(b_fv);
        let fab = d.apply(f_expr, &[a_local, b_local]);
        let fba = d.apply(f_expr, &[b_local, a_local]);
        let concl = d.bool_eq(fab, fba);
        let inner = d.pi_fv(b_fv, bool_ty, concl);
        d.pi_fv(a_fv, bool_ty, inner)
    };
    let hf_fv = d.fresh_fvar();
    let hf_expr = d.kernel().fvar(hf_fv);

    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let f_false_true = d.apply(f_expr, &[false_, true_]);
    let f_true_false = d.apply(f_expr, &[true_, false_]);
    let hf_false_true = d.apply(hf_expr, &[false_, true_]);
    let hf_true_false = d.apply(hf_expr, &[true_, false_]);

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, b: ExprId| {
        let bound_a = d.le(a, fuel);
        let bound_b = d.le(b, fuel);
        let lhs = bitwise_aux(d, &p, f_expr, fuel, a, b);
        let rhs = bitwise_aux(d, &p, f_expr, fuel, b, a);
        let concl = d.eq(lhs, rhs);
        let inner = d.arrow(bound_b, concl);
        d.arrow(bound_a, inner)
    };

    let base = |d: &mut NatDev<'_>, a: ExprId, b: ExprId| -> ExprId {
        let zero = d.zero();
        let bound_a_ty = d.le(a, zero);
        let bound_b_ty = d.le(b, zero);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let zero_le_a = d.lemma(p.zero_le, &[a]);
        let a_eq_zero = d.lemma(p.le_antisymm, &[a, zero, h1, zero_le_a]);
        let zero_le_b = d.lemma(p.zero_le, &[b]);
        let b_eq_zero = d.lemma(p.le_antisymm, &[b, zero, h2, zero_le_b]);

        let lhs = bitwise_aux(d, &p, f_expr, zero, a, b);
        let rhs = bitwise_aux(d, &p, f_expr, zero, b, a);
        let target = d.bool_select_nat(f_false_true, zero, zero);

        let lhs_congr = d.congr(b, zero, b_eq_zero, &|d, x| {
            d.bool_select_nat(f_false_true, x, zero)
        });
        let rhs_congr = d.congr(a, zero, a_eq_zero, &|d, x| {
            d.bool_select_nat(f_false_true, x, zero)
        });
        let rhs_congr_rev = d.symm(rhs, target, rhs_congr);
        let body = d.trans(lhs, target, rhs, lhs_congr, rhs_congr_rev);

        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
        d.lam_fv(h1_fv, bound_a_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId, b: ExprId| -> ExprId {
        let sk = d.succ(k);

        let goal_a = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound_a = d.le(candidate, sk);
            let bound_b = d.le(b, sk);
            let lhs = bitwise_aux(d, &p, f_expr, sk, candidate, b);
            let rhs = bitwise_aux(d, &p, f_expr, sk, b, candidate);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound_b, concl);
            d.arrow(bound_a, inner)
        };

        cases_zero_succ(
            d,
            a,
            &goal_a,
            &|d| {
                let zero = d.zero();
                let bound_a_ty = d.le(zero, sk);
                let bound_b_ty = d.le(b, sk);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();

                let lhs = bitwise_aux(d, &p, f_expr, sk, zero, b);
                let rhs = bitwise_aux(d, &p, f_expr, sk, b, zero);

                let lhs_is_target = d.lemma(p.bitwise_aux_zero_left_any_fuel, &[f_expr, sk, b]);
                let lhs_target = d.bool_select_nat(f_false_true, b, zero);
                let rhs_target = d.bool_select_nat(f_true_false, b, zero);
                let swap =
                    congr_bool_to_nat(d, f_false_true, f_true_false, hf_false_true, &|d, cond| {
                        d.bool_select_nat(cond, b, zero)
                    });
                let step1 = d.trans(lhs, lhs_target, rhs_target, lhs_is_target, swap);
                let rhs_refl = d.refl(rhs);
                let rhs_is_target_rev = d.symm(rhs, rhs_target, rhs_refl);
                let body = d.trans(lhs, rhs_target, rhs, step1, rhs_is_target_rev);

                let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
                d.lam_fv(h1_fv, bound_a_ty, with_h2)
            },
            &|d, a_pred| {
                let succ_a = d.succ(a_pred);

                let goal_b = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
                    let bound_a = d.le(succ_a, sk);
                    let bound_b = d.le(candidate, sk);
                    let lhs = bitwise_aux(d, &p, f_expr, sk, succ_a, candidate);
                    let rhs = bitwise_aux(d, &p, f_expr, sk, candidate, succ_a);
                    let concl = d.eq(lhs, rhs);
                    let inner = d.arrow(bound_b, concl);
                    d.arrow(bound_a, inner)
                };

                cases_zero_succ(
                    d,
                    b,
                    &goal_b,
                    &|d| {
                        let zero = d.zero();
                        let bound_a_ty = d.le(succ_a, sk);
                        let bound_b_ty = d.le(zero, sk);
                        let h1_fv = d.fresh_fvar();
                        let h2_fv = d.fresh_fvar();

                        let lhs = bitwise_aux(d, &p, f_expr, sk, succ_a, zero);
                        let rhs = bitwise_aux(d, &p, f_expr, sk, zero, succ_a);

                        let lhs_target = d.bool_select_nat(f_true_false, succ_a, zero);
                        let rhs_is_target =
                            d.lemma(p.bitwise_aux_zero_left_any_fuel, &[f_expr, sk, succ_a]);
                        let rhs_target = d.bool_select_nat(f_false_true, succ_a, zero);
                        let swap = congr_bool_to_nat(
                            d,
                            f_true_false,
                            f_false_true,
                            hf_true_false,
                            &|d, cond| d.bool_select_nat(cond, succ_a, zero),
                        );
                        let lhs_refl = d.refl(lhs);
                        let step1 = d.trans(lhs, lhs_target, rhs_target, lhs_refl, swap);
                        let rhs_is_target_rev = d.symm(rhs, rhs_target, rhs_is_target);
                        let body = d.trans(lhs, rhs_target, rhs, step1, rhs_is_target_rev);

                        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
                        d.lam_fv(h1_fv, bound_a_ty, with_h2)
                    },
                    &|d, b_pred| {
                        let succ_b = d.succ(b_pred);
                        let bound_a_ty = d.le(succ_a, sk);
                        let bound_b_ty = d.le(succ_b, sk);
                        let h1_fv = d.fresh_fvar();
                        let h1 = d.kernel().fvar(h1_fv);
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv);

                        let two = d.num(2);
                        let half_a = d.div(succ_a, two);
                        let half_b = d.div(succ_b, two);

                        let half_a_le_k = half_le_predecessor_of_succ(d, &p, a_pred, k, h1);
                        let half_b_le_k = half_le_predecessor_of_succ(d, &p, b_pred, k, h2);

                        let ih_at_halves = d.apply(ih, &[half_a, half_b]);
                        let ih_at_halves = d.apply(ih_at_halves, &[half_a_le_k, half_b_le_k]);

                        let rec = bitwise_aux(d, &p, f_expr, k, half_a, half_b);
                        let rec_swapped = bitwise_aux(d, &p, f_expr, k, half_b, half_a);

                        let one = d.num(1);
                        let zero = d.zero();
                        let bit_a = d.modulo(succ_a, two);
                        let bit_b = d.modulo(succ_b, two);
                        let bit_a_bool = d.beq(bit_a, one);
                        let bit_b_bool = d.beq(bit_b, one);
                        let combined = d.apply(f_expr, &[bit_a_bool, bit_b_bool]);
                        let combined_swapped = d.apply(f_expr, &[bit_b_bool, bit_a_bool]);
                        let bit = d.bool_select_nat(combined, one, zero);
                        let bit_swapped = d.bool_select_nat(combined_swapped, one, zero);
                        let bit_comm = bitwise_bit_comm(d, f_expr, hf_expr, succ_a, succ_b);

                        let start = guarded(d, succ_a, succ_b, succ_a, succ_b, rec, bit);
                        let mid = guarded(d, succ_a, succ_b, succ_a, succ_b, rec_swapped, bit);
                        let finish =
                            guarded(d, succ_a, succ_b, succ_a, succ_b, rec_swapped, bit_swapped);

                        let step1 = d.congr(rec, rec_swapped, ih_at_halves, &|d, hole| {
                            guarded(d, succ_a, succ_b, succ_a, succ_b, hole, bit)
                        });
                        let step2 = d.congr(bit, bit_swapped, bit_comm, &|d, hole| {
                            guarded(d, succ_a, succ_b, succ_a, succ_b, rec_swapped, hole)
                        });
                        let body = d.trans(start, mid, finish, step1, step2);

                        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
                        d.lam_fv(h1_fv, bound_a_ty, with_h2)
                    },
                )
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let applied = d.apply(proof_fn, &[a, b]);

    let ty_inner = {
        let body = statement(d, fuel, a, b);
        let with_b = d.pi_fv(b_fv, nat, body);
        let with_a = d.pi_fv(a_fv, nat, with_b);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value_inner = {
        let with_b = d.lam_fv(b_fv, nat, applied);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    let ty_hf = d.pi_fv(hf_fv, hf_ty, ty_inner);
    let value_hf = d.lam_fv(hf_fv, hf_ty, value_inner);
    let ty = d.pi_fv(f_fv, f_ty, ty_hf);
    let value = d.lam_fv(f_fv, f_ty, value_hf);
    d.declare_theorem(p.bitwise_aux_comm_of_fuel, ty, value)
}

/// `Nat.bitwise_comm : ∀ f, (∀ a b, Eq (f a b) (f b a)) → ∀ m n, Eq (bitwise
/// f m n) (bitwise f n m)` — `F:ml430-nat-bitwise-comm-1a273bae`. Routes
/// [`declare_bitwise_aux_comm_of_fuel`] and
/// [`declare_bitwise_aux_agree_of_fuel`] through the shared fuel `m + n`,
/// exactly as `land_comm`/`lor_comm` do (`rec_agreement.rs`).
pub(super) fn declare_bitwise_comm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_bitwise_aux_zero_left_any_fuel(d, p)?;
    declare_bitwise_aux_agree_of_fuel(d, p)?;
    declare_bitwise_aux_comm_of_fuel(d, p)?;
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let f_ty = {
        let inner = d.arrow(bool_ty, bool_ty);
        d.arrow(bool_ty, inner)
    };

    let f_fv = d.fresh_fvar();
    let f_expr = d.kernel().fvar(f_fv);
    let hf_ty = {
        let a_fv = d.fresh_fvar();
        let a_local = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b_local = d.kernel().fvar(b_fv);
        let fab = d.apply(f_expr, &[a_local, b_local]);
        let fba = d.apply(f_expr, &[b_local, a_local]);
        let concl = d.bool_eq(fab, fba);
        let inner = d.pi_fv(b_fv, bool_ty, concl);
        d.pi_fv(a_fv, bool_ty, inner)
    };
    let hf_fv = d.fresh_fvar();
    let hf_expr = d.kernel().fvar(hf_fv);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let sum = d.add(m, n);

    let le_refl_m = d.lemma(p.le_refl, &[m]);
    let m_le_sum = d.lemma(p.le_add_right, &[m, n]);
    let step_a = d.lemma(p.bitwise_aux_agree_of_fuel, &[f_expr, m, m, n, sum]);
    let step_a = d.apply(step_a, &[le_refl_m, m_le_sum]);
    // step_a : Eq (bitwiseAux f m m n) (bitwiseAux f sum m n)

    let le_refl_n = d.lemma(p.le_refl, &[n]);
    let n_le_n_sum = d.lemma(p.le_add_right, &[n, m]);
    let n_sum = d.add(n, m);
    let add_comm_nm = d.lemma(p.add_comm, &[n, m]);
    let n_le_motive = d.eq_motive(n_sum, &|d, x| d.le(n, x));
    let n_le_sum = d.transport(n_sum, n_le_motive, n_le_n_sum, sum, add_comm_nm);

    let step_b = d.lemma(p.bitwise_aux_comm_of_fuel, &[f_expr, hf_expr, sum, m, n]);
    let step_b = d.apply(step_b, &[m_le_sum, n_le_sum]);
    // step_b : Eq (bitwiseAux f sum m n) (bitwiseAux f sum n m)

    let step_c = d.lemma(p.bitwise_aux_agree_of_fuel, &[f_expr, n, n, m, sum]);
    let step_c = d.apply(step_c, &[le_refl_n, n_le_sum]);
    // step_c : Eq (bitwiseAux f n n m) (bitwiseAux f sum n m)

    let aux_m_m_n = bitwise_aux(d, &p, f_expr, m, m, n);
    let aux_sum_m_n = bitwise_aux(d, &p, f_expr, sum, m, n);
    let aux_sum_n_m = bitwise_aux(d, &p, f_expr, sum, n, m);
    let aux_n_n_m = bitwise_aux(d, &p, f_expr, n, n, m);

    let step_c_rev = d.symm(aux_n_n_m, aux_sum_n_m, step_c);
    let step_ab = d.trans(aux_m_m_n, aux_sum_m_n, aux_sum_n_m, step_a, step_b);
    let proof_body = d.trans(aux_m_m_n, aux_sum_n_m, aux_n_n_m, step_ab, step_c_rev);

    let lhs = bitwise(d, &p, f_expr, m, n);
    let rhs = bitwise(d, &p, f_expr, n, m);
    let stmt = d.eq(lhs, rhs);

    let ty_mn = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(m_fv, nat, with_n)
    };
    let value_mn = {
        let with_n = d.lam_fv(n_fv, nat, proof_body);
        d.lam_fv(m_fv, nat, with_n)
    };
    let ty_hf = d.pi_fv(hf_fv, hf_ty, ty_mn);
    let value_hf = d.lam_fv(hf_fv, hf_ty, value_mn);
    let ty = d.pi_fv(f_fv, f_ty, ty_hf);
    let value = d.lam_fv(f_fv, f_ty, value_hf);
    d.declare_theorem(p.bitwise_comm, ty, value)
}

// ============================================================================
// `Nat.bitwise_swap` — `bitwise (swap f) m n = bitwise f n m` (Mathlib states
// this as a `Function.swap` function equality; this kernel has no `funext`,
// so it is stated pointwise, as every other function-equality fact in this
// prelude is).
//
// Simpler than `bitwise_comm`, and it is worth recording why: `swap f`
// applied to any two `Bool`s beta-reduces DIRECTLY to `f` applied to them in
// the other order, because the swap is baked into which function gets
// applied rather than asserted about a fixed one. So every site
// `bitwise_comm` needed `hf` + `congr_bool_to_nat` for — the two boundary
// rows AND the per-bit combine — becomes pure defeq here: `d.refl`, or a
// lemma instantiated at `swap f` whose conclusion beta-reduces to what the
// other side needs. Confirmed by hand (not Python — the recursion is small
// enough to trace by substitution) before writing any Rust: expanding
// `bitwiseAux (swap f) fuel m n` and `bitwiseAux f fuel n m` case-by-case
// shows every row matches by beta/iota alone except the both-nonzero
// recursive step, which needs exactly the induction hypothesis (the "bit"
// term there matches the other side exactly too, so only the recursive
// sub-call needs `d.congr`).
// ============================================================================

/// `fun a b => f_expr b a` — `Function.swap f` (Mathlib), built inline (this
/// prelude declares no top-level `Function.swap`). Whenever this is
/// substituted for `f` inside `bitwiseAux`'s body, every application
/// `swap_f x y` beta-reduces DIRECTLY to `f_expr y x` — no propositional
/// lemma is needed to "swap under `f`", unlike `bitwise_comm`'s
/// `hf`-mediated swaps, because the swap here is baked into which function
/// is applied, not asserted about a fixed one.
pub(super) fn swap_fn<D: NatOps>(d: &mut D, f_expr: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let body = d.apply(f_expr, &[b, a]);
    let with_b = d.lam_fv(b_fv, bool_ty, body);
    d.lam_fv(a_fv, bool_ty, with_b)
}

/// `bitwise_aux_swap_of_fuel : ∀ f fuel m n, Le m fuel → Le n fuel → Eq
/// (bitwiseAux (swap f) fuel m n) (bitwiseAux f fuel n m)` — the `swap`
/// counterpart of [`declare_bitwise_aux_comm_of_fuel`], and strictly
/// simpler: NO `hf` hypothesis is needed (see the section doc). Same
/// case-split skeleton (`cases_zero_succ` on `m` then, inside the `succ`
/// branch, on `n`); only the both-nonzero step needs the induction
/// hypothesis, via a single `d.congr` on the recursive sub-call — the "bit"
/// term matches the other side exactly by the same beta-swap, so no
/// `bit`-side congruence is needed.
fn declare_bitwise_aux_swap_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let f_ty = {
        let inner = d.arrow(bool_ty, bool_ty);
        d.arrow(bool_ty, inner)
    };

    let f_fv = d.fresh_fvar();
    let f_expr = d.kernel().fvar(f_fv);
    let swap_f = swap_fn(d, f_expr);

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, b: ExprId| {
        let bound_a = d.le(a, fuel);
        let bound_b = d.le(b, fuel);
        let lhs = bitwise_aux(d, &p, swap_f, fuel, a, b);
        let rhs = bitwise_aux(d, &p, f_expr, fuel, b, a);
        let concl = d.eq(lhs, rhs);
        let inner = d.arrow(bound_b, concl);
        d.arrow(bound_a, inner)
    };

    // fuel = 0: `Le a 0`/`Le b 0` force `a = b = 0`. `lhs` reduces (fuel = 0
    // ignores the fuel-arg `a`) to `bool_select_nat (swap_f false true) b 0`
    // ≡ `bool_select_nat (f true false) b 0`; `rhs` reduces (ignoring `b`,
    // the fuel-arg here) to `bool_select_nat (f false true) a 0`. Different
    // conditions AND different values — genuinely need `a = 0, b = 0` to
    // collapse both to the shared value `0` via `bool_select_nat_same`,
    // exactly `bitwise_aux_comm_of_fuel`'s base case's shape.
    let base = |d: &mut NatDev<'_>, a: ExprId, b: ExprId| -> ExprId {
        let zero = d.zero();
        let bound_a_ty = d.le(a, zero);
        let bound_b_ty = d.le(b, zero);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let zero_le_a = d.lemma(p.zero_le, &[a]);
        let a_eq_zero = d.lemma(p.le_antisymm, &[a, zero, h1, zero_le_a]);
        let zero_le_b = d.lemma(p.zero_le, &[b]);
        let b_eq_zero = d.lemma(p.le_antisymm, &[b, zero, h2, zero_le_b]);

        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let f_true_false = d.apply(f_expr, &[true_, false_]);
        let f_false_true = d.apply(f_expr, &[false_, true_]);

        let lhs = bitwise_aux(d, &p, swap_f, zero, a, b);
        let rhs = bitwise_aux(d, &p, f_expr, zero, b, a);

        let lhs_target = d.bool_select_nat(f_true_false, zero, zero);
        let rhs_target = d.bool_select_nat(f_false_true, zero, zero);

        let lhs_congr = d.congr(b, zero, b_eq_zero, &|d, x| {
            d.bool_select_nat(f_true_false, x, zero)
        });
        let rhs_congr = d.congr(a, zero, a_eq_zero, &|d, x| {
            d.bool_select_nat(f_false_true, x, zero)
        });
        let rhs_congr_rev = d.symm(rhs, rhs_target, rhs_congr);

        let lhs_target_zero = bool_select_nat_same(d, &p, f_true_false, zero);
        let rhs_target_zero = bool_select_nat_same(d, &p, f_false_true, zero);
        let zero_eq_rhs_target = d.symm(rhs_target, zero, rhs_target_zero);

        let lhs_to_zero = d.trans(lhs, lhs_target, zero, lhs_congr, lhs_target_zero);
        let zero_to_rhs = d.trans(zero, rhs_target, rhs, zero_eq_rhs_target, rhs_congr_rev);
        let body = d.trans(lhs, zero, rhs, lhs_to_zero, zero_to_rhs);

        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
        d.lam_fv(h1_fv, bound_a_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId, b: ExprId| -> ExprId {
        let sk = d.succ(k);

        let goal_a = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound_a = d.le(candidate, sk);
            let bound_b = d.le(b, sk);
            let lhs = bitwise_aux(d, &p, swap_f, sk, candidate, b);
            let rhs = bitwise_aux(d, &p, f_expr, sk, b, candidate);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound_b, concl);
            d.arrow(bound_a, inner)
        };

        cases_zero_succ(
            d,
            a,
            &goal_a,
            // a = 0: `lhs = bitwiseAux (swap_f) sk 0 b` is exactly
            // `bitwise_aux_zero_left_any_fuel`'s shape at `f := swap_f`;
            // its conclusion beta-reduces (`swap_f false true ≡
            // f true false`) to exactly what `rhs = bitwiseAux f sk b 0`
            // reduces to via pure iota (outer guard `beq 0 0` is a literal
            // `true`) — so the lemma applied at `swap_f` IS the proof,
            // no further bridging needed.
            &|d| {
                let zero = d.zero();
                let bound_a_ty = d.le(zero, sk);
                let bound_b_ty = d.le(b, sk);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();
                let body = d.lemma(p.bitwise_aux_zero_left_any_fuel, &[swap_f, sk, b]);
                let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
                d.lam_fv(h1_fv, bound_a_ty, with_h2)
            },
            &|d, a_pred| {
                let succ_a = d.succ(a_pred);

                let goal_b = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
                    let bound_a = d.le(succ_a, sk);
                    let bound_b = d.le(candidate, sk);
                    let lhs = bitwise_aux(d, &p, swap_f, sk, succ_a, candidate);
                    let rhs = bitwise_aux(d, &p, f_expr, sk, candidate, succ_a);
                    let concl = d.eq(lhs, rhs);
                    let inner = d.arrow(bound_b, concl);
                    d.arrow(bound_a, inner)
                };

                cases_zero_succ(
                    d,
                    b,
                    &goal_b,
                    // b = 0, a = succ_a: BOTH sides reduce (pure iota — `sk`
                    // and `succ_a` are both literally `succ`-shaped, `0` is
                    // a literal) to `bool_select_nat (f false true) succ_a
                    // 0` — a plain `d.refl`, no lemma needed.
                    &|d| {
                        let zero = d.zero();
                        let bound_a_ty = d.le(succ_a, sk);
                        let bound_b_ty = d.le(zero, sk);
                        let h1_fv = d.fresh_fvar();
                        let h2_fv = d.fresh_fvar();
                        let lhs = bitwise_aux(d, &p, swap_f, sk, succ_a, zero);
                        let body = d.refl(lhs);
                        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
                        d.lam_fv(h1_fv, bound_a_ty, with_h2)
                    },
                    // succ_a, succ_b: both guards resolve to `false` by pure
                    // iota (both operands are literally `succ`-shaped), so
                    // both sides reduce to `2 * <recursive> + bit`, with the
                    // SAME `bit` term on both sides (by the same beta-swap
                    // as the base case) — only the recursive sub-call needs
                    // the induction hypothesis.
                    &|d, b_pred| {
                        let succ_b = d.succ(b_pred);
                        let bound_a_ty = d.le(succ_a, sk);
                        let bound_b_ty = d.le(succ_b, sk);
                        let h1_fv = d.fresh_fvar();
                        let h1 = d.kernel().fvar(h1_fv);
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv);

                        let two = d.num(2);
                        let half_a = d.div(succ_a, two);
                        let half_b = d.div(succ_b, two);

                        let half_a_le_k = half_le_predecessor_of_succ(d, &p, a_pred, k, h1);
                        let half_b_le_k = half_le_predecessor_of_succ(d, &p, b_pred, k, h2);

                        let ih_at_halves = d.apply(ih, &[half_a, half_b]);
                        let ih_at_halves = d.apply(ih_at_halves, &[half_a_le_k, half_b_le_k]);
                        // ih_at_halves : Eq (bitwiseAux swap_f k half_a
                        // half_b) (bitwiseAux f_expr k half_b half_a)

                        let one = d.num(1);
                        let zero = d.zero();
                        let bit_a = d.modulo(succ_a, two);
                        let bit_b = d.modulo(succ_b, two);
                        let bit_a_bool = d.beq(bit_a, one);
                        let bit_b_bool = d.beq(bit_b, one);
                        // `f (beq(succ_b%2,1)) (beq(succ_a%2,1))` — matches
                        // BOTH sides: the LHS's `swap_f (beq(a%2,1))
                        // (beq(b%2,1))` beta-reduces to exactly this, and
                        // the RHS's own bit formula (with M'=succ_b,
                        // N'=succ_a) computes exactly this directly.
                        let combined = d.apply(f_expr, &[bit_b_bool, bit_a_bool]);
                        let bit_term = d.bool_select_nat(combined, one, zero);

                        let rec_lhs = bitwise_aux(d, &p, swap_f, k, half_a, half_b);
                        let rec_rhs = bitwise_aux(d, &p, f_expr, k, half_b, half_a);

                        let proof = d.congr(rec_lhs, rec_rhs, ih_at_halves, &|d, hole| {
                            let doubled = d.mul(two, hole);
                            d.add(doubled, bit_term)
                        });
                        // proof : Eq (2*rec_lhs+bit_term) (2*rec_rhs+bit_term),
                        // defeq to Eq (bitwiseAux swap_f sk succ_a succ_b)
                        // (bitwiseAux f_expr sk succ_b succ_a).

                        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, proof);
                        d.lam_fv(h1_fv, bound_a_ty, with_h2)
                    },
                )
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let applied = d.apply(proof_fn, &[a, b]);

    let ty_inner = {
        let body = statement(d, fuel, a, b);
        let with_b = d.pi_fv(b_fv, nat, body);
        let with_a = d.pi_fv(a_fv, nat, with_b);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value_inner = {
        let with_b = d.lam_fv(b_fv, nat, applied);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    let ty = d.pi_fv(f_fv, f_ty, ty_inner);
    let value = d.lam_fv(f_fv, f_ty, value_inner);
    d.declare_theorem(p.bitwise_aux_swap_of_fuel, ty, value)
}

/// `Nat.bitwise_swap : ∀ f m n, Eq (bitwise (swap f) m n) (bitwise f n m)`
/// — `F:ml430-nat-bitwise-swap-7175e90e`. Routes
/// [`declare_bitwise_aux_swap_of_fuel`] and the ALREADY-DECLARED
/// [`NatPrelude::bitwise_aux_agree_of_fuel`] (from [`declare_bitwise_comm`],
/// which this function's dispatch is placed after) through the shared fuel
/// `m + n`, exactly as `bitwise_comm`'s own final assembly — but simpler:
/// no `hf` hypothesis anywhere.
pub(super) fn declare_bitwise_swap(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_bitwise_aux_swap_of_fuel(d, p)?;
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let f_ty = {
        let inner = d.arrow(bool_ty, bool_ty);
        d.arrow(bool_ty, inner)
    };

    let f_fv = d.fresh_fvar();
    let f_expr = d.kernel().fvar(f_fv);
    let swap_f = swap_fn(d, f_expr);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let sum = d.add(m, n);

    let le_refl_m = d.lemma(p.le_refl, &[m]);
    let m_le_sum = d.lemma(p.le_add_right, &[m, n]);
    let step_a = d.lemma(p.bitwise_aux_agree_of_fuel, &[swap_f, m, m, n, sum]);
    let step_a = d.apply(step_a, &[le_refl_m, m_le_sum]);
    // step_a : Eq (bitwiseAux swap_f m m n) (bitwiseAux swap_f sum m n)

    let le_refl_n = d.lemma(p.le_refl, &[n]);
    let n_le_n_sum = d.lemma(p.le_add_right, &[n, m]);
    let n_sum = d.add(n, m);
    let add_comm_nm = d.lemma(p.add_comm, &[n, m]);
    let n_le_motive = d.eq_motive(n_sum, &|d, x| d.le(n, x));
    let n_le_sum = d.transport(n_sum, n_le_motive, n_le_n_sum, sum, add_comm_nm);

    let step_b = d.lemma(p.bitwise_aux_swap_of_fuel, &[f_expr, sum, m, n]);
    let step_b = d.apply(step_b, &[m_le_sum, n_le_sum]);
    // step_b : Eq (bitwiseAux swap_f sum m n) (bitwiseAux f_expr sum n m)

    let step_c = d.lemma(p.bitwise_aux_agree_of_fuel, &[f_expr, n, n, m, sum]);
    let step_c = d.apply(step_c, &[le_refl_n, n_le_sum]);
    // step_c : Eq (bitwiseAux f_expr n n m) (bitwiseAux f_expr sum n m)

    let aux_swap_m_m_n = bitwise_aux(d, &p, swap_f, m, m, n);
    let aux_swap_sum_m_n = bitwise_aux(d, &p, swap_f, sum, m, n);
    let aux_f_sum_n_m = bitwise_aux(d, &p, f_expr, sum, n, m);
    let aux_f_n_n_m = bitwise_aux(d, &p, f_expr, n, n, m);

    let step_c_rev = d.symm(aux_f_n_n_m, aux_f_sum_n_m, step_c);
    let step_ab = d.trans(
        aux_swap_m_m_n,
        aux_swap_sum_m_n,
        aux_f_sum_n_m,
        step_a,
        step_b,
    );
    let proof_body = d.trans(
        aux_swap_m_m_n,
        aux_f_sum_n_m,
        aux_f_n_n_m,
        step_ab,
        step_c_rev,
    );

    let lhs = bitwise(d, &p, swap_f, m, n);
    let rhs = bitwise(d, &p, f_expr, n, m);
    let stmt = d.eq(lhs, rhs);

    let ty_mn = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(m_fv, nat, with_n)
    };
    let value_mn = {
        let with_n = d.lam_fv(n_fv, nat, proof_body);
        d.lam_fv(m_fv, nat, with_n)
    };
    let ty = d.pi_fv(f_fv, f_ty, ty_mn);
    let value = d.lam_fv(f_fv, f_ty, value_mn);
    d.declare_theorem(p.bitwise_swap, ty, value)
}

// ============================================================================
// `Nat.bitwise_bit'` — the generic-`f` counterpart of `bit_decode.rs`'s
// `land_bit`/`lor_bit`/`ldiff_bit`: `bitwise f (bit a m) (bit b n) = bit (f a
// b) (bitwise f m n)`, given `(m = 0 -> a = true)` and `(n = 0 -> b =
// true)`. `F:ml430-nat-bitwise-bit-4c4b28a8`.
//
// The fuel-swap machinery (`base`/`k1`/`fuel`, both `Le` bounds, the
// `Nat.bit_div_two`/`Nat.bit_mod_two` decode) is IDENTICAL to `land_bit`'s —
// it never inspects an operator's absorbing zero, only `Nat.bit`'s own
// encoding, so it transports unchanged (see `bit_decode.rs`'s module doc).
// Two things are new, both specific to a SYMBOLIC `f`:
//
// 1. The per-bit combine converts each raw `Nat.mod _ 2` bit to `Bool` via
//    `beq _ 1` (`bitwiseAux`'s own ad hoc `bodd`) before applying `f`, while
//    `Nat.bit_mod_two` decodes the SAME raw `mod` term to `bool_select_nat
//    test 1 0`. These two encodings must be shown to cancel —
//    [`cond_beq_one_eq_self`] below — before the combine matches `f a b`.
//    `land`/`lor`/`ldiff`'s OWN combines never round-trip through `Bool`
//    (they stay in `{0,1} : Nat` throughout), so this step has no analogue
//    in `bit_decode.rs`.
// 2. The two side hypotheses close a genuine ambiguity the FIXED-`f`
//    specializations never have. `bitwiseAux`'s `n = 0` boundary row
//    returns the WHOLE bit-encoded operand `bit a m`, not a per-operator
//    absorbing constant, so at `a = false, m = 0` a misbehaved `f` (e.g.
//    the constant-`true` function) can make the claim false; the
//    hypothesis rules out exactly that leading-zero encoding.
// ============================================================================

/// `Eq Bool (beq (bool_select_nat x 1 0) 1) x` — round-tripping a `Bool`
/// through [`NatOps::bool_select_nat`]'s `{0,1}` encoding and back through
/// `Nat.beq _ 1` recovers the original value. Two-leaf `Bool` split; both
/// branches close by `refl` (`beq 1 1`/`beq 0 1` both compute against small
/// literals). See the section doc for why this is needed here and nowhere
/// else in this file.
fn cond_beq_one_eq_self(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        x,
        &|d, cand| {
            let one = d.num(1);
            let zero = d.zero();
            let cond = d.bool_select_nat(cand, one, zero);
            let lhs = d.beq(cond, one);
            d.bool_eq(lhs, cand)
        },
        &|d| {
            let true_ = d.bool_true();
            let one = d.num(1);
            let zero = d.zero();
            let cond = d.bool_select_nat(true_, one, zero);
            let lhs = d.beq(cond, one);
            d.bool_refl(lhs)
        },
        &|d| {
            let false_ = d.bool_false();
            let one = d.num(1);
            let zero = d.zero();
            let cond = d.bool_select_nat(false_, one, zero);
            let lhs = d.beq(cond, one);
            d.bool_refl(lhs)
        },
    )
}

/// `bool_select_nat (f a b) 1 0` — the target per-bit value the general
/// combine collapses to once both raw `Nat.mod _ 2` bits are decoded
/// through `Nat.bit_mod_two` and [`cond_beq_one_eq_self`] undoes the
/// `beq _ 1` conversion.
fn bitwise_bit_combine(d: &mut NatDev<'_>, f_expr: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    let fab = d.apply(f_expr, &[a, b]);
    d.bool_select_nat(fab, one, zero)
}

/// `add (mul 2 bitwise_mn) (bitwise_bit_combine f a b)` — defeq to `bit (f a
/// b) bitwise_mn`, the theorem's literal RHS (`Nat.bit`'s own definition,
/// `bits.rs`). Kept as its own function since it recurs at every leaf of
/// the guard-resolution tree below.
fn bitwise_bit_stepped(
    d: &mut NatDev<'_>,
    f_expr: ExprId,
    a: ExprId,
    b: ExprId,
    bitwise_mn: ExprId,
) -> ExprId {
    let two = d.num(2);
    let doubled = d.mul(two, bitwise_mn);
    let bitval = bitwise_bit_combine(d, f_expr, a, b);
    d.add(doubled, bitval)
}

/// `Eq (guarded (bit a m) (bit b n) on_n_zero on_m_zero bitwise_mn bitgen)
/// (bitwise_bit_stepped f a b bitwise_mn)` — the guard-resolution half of
/// the bridge (the `bitwise` twin of `bit_decode.rs`'s `land_guard_goal`),
/// once the fuel machinery and the per-bit combine have already rewritten
/// the recursive occurrence down to the opaque `bitwise_mn := bitwise f m
/// n` and the bit value down to `f a b`. `bitwise_mn` is carried through
/// unopened — this proof never needs its value, only that it is the SAME
/// term on both sides.
#[allow(clippy::too_many_arguments)]
fn bitwise_bit_goal(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f_expr: ExprId,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
    bitwise_mn: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let bit_am = d.const_app(p.bit, &[a, m]);
    let bit_bn = d.const_app(p.bit, &[b, n]);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let f_true_false = d.apply(f_expr, &[true_, false_]);
    let f_false_true = d.apply(f_expr, &[false_, true_]);
    let on_n_zero = d.bool_select_nat(f_true_false, bit_am, zero);
    let on_m_zero = d.bool_select_nat(f_false_true, bit_bn, zero);
    let bitval = bitwise_bit_combine(d, f_expr, a, b);
    let lhs = guarded(d, bit_am, bit_bn, on_n_zero, on_m_zero, bitwise_mn, bitval);
    let rhs = bitwise_bit_stepped(d, f_expr, a, b, bitwise_mn);
    d.eq(lhs, rhs)
}

/// [`cases_zero_succ`], but additionally threads an equation `Eq x
/// <candidate>` into each branch — the "generalize with equality" trick
/// needed wherever a hypothesis about the ORIGINAL scrutinee `x` (not the
/// branch's substituted literal) must be applied inside that branch.
/// `cases_zero_succ`'s own doc names this explicitly: "a caller wanting a
/// hypothesis usable inside a branch must fold it into `motive` and
/// re-introduce it per branch." [`bitwise_guard_inner`] and
/// [`resolve_bitwise_bit_guard`] are exactly such callers — each applies
/// `hm`/`hn` at the leaf this produces the equation for.
fn cases_zero_succ_with_eq(
    d: &mut NatDev<'_>,
    x: ExprId,
    goal: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    at_zero: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    at_succ: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let full = cases_zero_succ(
        d,
        x,
        &|d, cand| {
            let heq_ty = d.eq(x, cand);
            let g = goal(d, cand);
            d.arrow(heq_ty, g)
        },
        &|d| {
            let zero = d.zero();
            let heq_ty = d.eq(x, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = at_zero(d, h);
            d.lam_fv(h_fv, heq_ty, body)
        },
        &|d, pred| {
            let succ_pred = d.succ(pred);
            let heq_ty = d.eq(x, succ_pred);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = at_succ(d, pred, h);
            d.lam_fv(h_fv, heq_ty, body)
        },
    );
    let refl_x = d.refl(x);
    d.apply(full, &[refl_x])
}

/// Resolves the `m`-guard given the `n`-guard already known to reduce false
/// at the caller's chosen `(b, n)` — returns a proof of `(Eq m 0 -> Eq a
/// true) -> [bitwise_bit_goal]`.
///
/// Mirrors `bit_decode.rs`'s `land_guard_inner` (split on `a` first, since
/// `bit a m`'s SECOND slot is `Nat.add`'s recursion argument — `a = true`
/// makes `bit a m` succ-shaped for ANY `m`), but for a symbolic `f` the `a =
/// false, m = 0` leaf is not `land`'s absorbing-zero row: it is the genuine
/// ambiguity the section doc's counterexample exploits, closed instead by
/// folding `hm`'s conclusion through the `a`-split (using the branch's own
/// candidate, so no separate "remember" is needed for `a`) and, once inside
/// `a = false`, using [`cases_zero_succ_with_eq`] on `m` to recover `Eq m 0`
/// for `hm`'s domain. Combining the two gives `Eq Bool false true`, and
/// [`NatOps::false_true_elim`] closes the rest.
#[allow(clippy::too_many_arguments)]
fn bitwise_guard_inner(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f_expr: ExprId,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
    bitwise_mn: ExprId,
) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| {
            let zero = d.zero();
            let eqm0 = d.eq(m, zero);
            let true_ = d.bool_true();
            let concl = d.bool_eq(cand_a, true_);
            let hm_arrow = d.arrow(eqm0, concl);
            let goal = bitwise_bit_goal(d, &p, f_expr, cand_a, m, b, n, bitwise_mn);
            d.arrow(hm_arrow, goal)
        },
        &|d| {
            let true_ = d.bool_true();
            let zero = d.zero();
            let eqm0 = d.eq(m, zero);
            let true_eq_true = d.bool_eq(true_, true_);
            let hm_ty = d.arrow(eqm0, true_eq_true);
            let h_fv = d.fresh_fvar();
            let stepped = bitwise_bit_stepped(d, f_expr, true_, b, bitwise_mn);
            let body = d.refl(stepped);
            d.lam_fv(h_fv, hm_ty, body)
        },
        &|d| {
            let false_ = d.bool_false();
            let zero = d.zero();
            let eqm0 = d.eq(m, zero);
            let true_ = d.bool_true();
            let false_eq_true = d.bool_eq(false_, true_);
            let hm_ty_false = d.arrow(eqm0, false_eq_true);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = cases_zero_succ_with_eq(
                d,
                m,
                &|d, cand_m| bitwise_bit_goal(d, &p, f_expr, false_, cand_m, b, n, bitwise_mn),
                &|d, heq_m| {
                    let contra = d.apply(h, &[heq_m]);
                    let target = {
                        let zero = d.zero();
                        bitwise_bit_goal(d, &p, f_expr, false_, zero, b, n, bitwise_mn)
                    };
                    d.false_true_elim(target, contra)
                },
                &|d, m_pred, _heq_m| {
                    let succ_m = d.succ(m_pred);
                    let _ = succ_m;
                    let stepped = bitwise_bit_stepped(d, f_expr, false_, b, bitwise_mn);
                    d.refl(stepped)
                },
            );
            d.lam_fv(h_fv, hm_ty_false, body)
        },
    )
}

/// Resolves BOTH guards of `bitwiseAux f (succ k1) (bit a m) (bit b n)`'s
/// step row against the theorem's target, given the side hypotheses
/// `hm`/`hn`. Splits `b` first (`bit b n`'s SECOND slot is `Nat.add`'s
/// recursion argument, so `b = true` resolves the `n`-guard false for ANY
/// `n`), then (at `b = false`) `n` itself via [`cases_zero_succ_with_eq`],
/// closing the `n = 0` leaf via `hn` exactly as [`bitwise_guard_inner`]
/// closes its own `m = 0` leaf via `hm`. Returns `GOAL(a, m, b, n)`
/// directly (both hypothesis arrows are applied here, at the point each is
/// consumed).
#[allow(clippy::too_many_arguments)]
fn resolve_bitwise_bit_guard(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f_expr: ExprId,
    hm: ExprId,
    hn: ExprId,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
    bitwise_mn: ExprId,
) -> ExprId {
    let p = *p;
    let full = case_bool(
        d,
        &p,
        b,
        &|d, cand_b| {
            let zero = d.zero();
            let eqn0 = d.eq(n, zero);
            let true_ = d.bool_true();
            let concl = d.bool_eq(cand_b, true_);
            let hn_arrow = d.arrow(eqn0, concl);
            let goal = bitwise_bit_goal(d, &p, f_expr, a, m, cand_b, n, bitwise_mn);
            d.arrow(hn_arrow, goal)
        },
        &|d| {
            let true_ = d.bool_true();
            let zero = d.zero();
            let eqn0 = d.eq(n, zero);
            let true_eq_true = d.bool_eq(true_, true_);
            let hn_ty = d.arrow(eqn0, true_eq_true);
            let h_fv = d.fresh_fvar();
            let inner = bitwise_guard_inner(d, &p, f_expr, a, m, true_, n, bitwise_mn);
            let applied = d.apply(inner, &[hm]);
            d.lam_fv(h_fv, hn_ty, applied)
        },
        &|d| {
            let false_ = d.bool_false();
            let zero = d.zero();
            let eqn0 = d.eq(n, zero);
            let true_ = d.bool_true();
            let false_eq_true = d.bool_eq(false_, true_);
            let hn_ty_false = d.arrow(eqn0, false_eq_true);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = cases_zero_succ_with_eq(
                d,
                n,
                &|d, cand_n| bitwise_bit_goal(d, &p, f_expr, a, m, false_, cand_n, bitwise_mn),
                &|d, heq_n| {
                    let contra = d.apply(h, &[heq_n]);
                    let target = {
                        let zero = d.zero();
                        bitwise_bit_goal(d, &p, f_expr, a, m, false_, zero, bitwise_mn)
                    };
                    d.false_true_elim(target, contra)
                },
                &|d, n_pred, _heq_n| {
                    let succ_n = d.succ(n_pred);
                    let inner =
                        bitwise_guard_inner(d, &p, f_expr, a, m, false_, succ_n, bitwise_mn);
                    d.apply(inner, &[hm])
                },
            );
            d.lam_fv(h_fv, hn_ty_false, body)
        },
    );
    d.apply(full, &[hn])
}

/// `Nat.bitwise_bit' : ∀ f (a : Bool) (m : Nat) (b : Bool) (n : Nat), (Eq m
/// 0 -> Eq a true) -> (Eq n 0 -> Eq b true) -> Eq (bitwise f (bit a m) (bit
/// b n)) (bit (f a b) (bitwise f m n))` — `F:ml430-nat-bitwise-bit-4c4b28a8`.
/// See the section doc above for the construction.
pub(super) fn declare_bitwise_bit(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let f_ty = {
        let inner = d.arrow(bool_ty, bool_ty);
        d.arrow(bool_ty, inner)
    };

    let f_fv = d.fresh_fvar();
    let f_expr = d.kernel().fvar(f_fv);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hm_ty = {
        let zero = d.zero();
        let eqm0 = d.eq(m, zero);
        let true_ = d.bool_true();
        let concl = d.bool_eq(a, true_);
        d.arrow(eqm0, concl)
    };
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let hn_ty = {
        let zero = d.zero();
        let eqn0 = d.eq(n, zero);
        let true_ = d.bool_true();
        let concl = d.bool_eq(b, true_);
        d.arrow(eqn0, concl)
    };
    let hn_fv = d.fresh_fvar();
    let hn = d.kernel().fvar(hn_fv);

    let two = d.num(2);

    let base = d.mul(two, m);
    let k1 = d.succ(base);
    let fuel = d.succ(k1);

    let bit_am = d.const_app(p.bit, &[a, m]);
    let bit_bn = d.const_app(p.bit, &[b, n]);

    // --- Le (bit a m) fuel, via case split on a (identical to land_bit) ----
    let m_le_k1 = case_bool(
        d,
        &p,
        a,
        &|d, x| {
            let bam = d.const_app(p.bit, &[x, m]);
            d.le(bam, k1)
        },
        &|d| d.lemma(p.le_refl, &[k1]),
        &|d| d.lemma(p.le_succ, &[base]),
    );
    let k1_le_fuel = d.lemma(p.le_succ, &[k1]);
    let m_le_fuel = d.lemma(p.le_trans, &[bit_am, k1, fuel, m_le_k1, k1_le_fuel]);

    // --- Le m k1 (identical to land_bit) ------------------------------------
    let mm = d.add(m, m);
    let m_le_mm = d.lemma(p.le_add_right, &[m, m]);
    let two_mul_eq = two_mul_eq_add_self(d, &p, m); // Eq base mm
    let mm_eq_base = d.symm(base, mm, two_mul_eq);
    let motive_le = d.eq_motive(mm, &|d, x| d.le(m, x));
    let m_le_base = d.transport(mm, motive_le, m_le_mm, base, mm_eq_base);
    let base_le_k1 = d.lemma(p.le_succ, &[base]);
    let m_le_k1_bound = d.lemma(p.le_trans, &[m, base, k1, m_le_base, base_le_k1]);

    // --- bitwise f (bit a m)(bit b n) = bitwiseAux f fuel (bit a m)(bit b n)
    let le_refl_bit_am = d.lemma(p.le_refl, &[bit_am]);
    let step0 = d.lemma(
        p.bitwise_aux_agree_of_fuel,
        &[f_expr, bit_am, bit_am, bit_bn, fuel],
    );
    let step0 = d.apply(step0, &[le_refl_bit_am, m_le_fuel]);
    let bitwise_ab = bitwise(d, &p, f_expr, bit_am, bit_bn);
    let aux_fuel = bitwise_aux(d, &p, f_expr, fuel, bit_am, bit_bn);

    // --- refl-unfold to guarded(...) at the raw div/mod subterms -----------
    let half_am = d.div(bit_am, two);
    let half_bn = d.div(bit_bn, two);
    let mod_am = d.modulo(bit_am, two);
    let mod_bn = d.modulo(bit_bn, two);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let f_true_false = d.apply(f_expr, &[true_, false_]);
    let f_false_true = d.apply(f_expr, &[false_, true_]);
    let zero = d.zero();
    let on_n_zero0 = d.bool_select_nat(f_true_false, bit_am, zero);
    let on_m_zero0 = d.bool_select_nat(f_false_true, bit_bn, zero);
    let rec0 = bitwise_aux(d, &p, f_expr, k1, half_am, half_bn);
    let one = d.num(1);
    let mod_am_bool = d.beq(mod_am, one);
    let mod_bn_bool = d.beq(mod_bn, one);
    let combined0 = d.apply(f_expr, &[mod_am_bool, mod_bn_bool]);
    let bitval0 = d.bool_select_nat(combined0, one, zero);
    let guarded0 = guarded(d, bit_am, bit_bn, on_n_zero0, on_m_zero0, rec0, bitval0);
    let step1 = d.refl(aux_fuel);

    // --- rewrite half_am -> m, half_bn -> n, then aux k1 m n -> bitwise m n
    let div_a = d.lemma(p.bit_div_two, &[a, m]);
    let div_b = d.lemma(p.bit_div_two, &[b, n]);
    let bitwise_mn = bitwise(d, &p, f_expr, m, n);

    let rec1 = bitwise_aux(d, &p, f_expr, k1, m, half_bn);
    let rec0_to_rec1 = d.congr(half_am, m, div_a, &|d, x| {
        bitwise_aux(d, &p, f_expr, k1, x, half_bn)
    });
    let rec2 = bitwise_aux(d, &p, f_expr, k1, m, n);
    let rec1_to_rec2 = d.congr(half_bn, n, div_b, &|d, x| {
        bitwise_aux(d, &p, f_expr, k1, m, x)
    });
    let le_refl_m = d.lemma(p.le_refl, &[m]);
    let rec2_eq_bitwise_mn = d.lemma(p.bitwise_aux_agree_of_fuel, &[f_expr, k1, m, n, m]);
    let rec2_eq_bitwise_mn = d.apply(rec2_eq_bitwise_mn, &[m_le_k1_bound, le_refl_m]);
    let (_rec_final, rec_chain) = d.chain(
        rec0,
        &[
            (rec1, rec0_to_rec1),
            (rec2, rec1_to_rec2),
            (bitwise_mn, rec2_eq_bitwise_mn),
        ],
    );

    // --- rewrite mod_am -> cond a, mod_bn -> cond b, then undo the beq/1 ---
    // conversion to recover `f a b` (needed here and nowhere else in this
    // file — see the section doc).
    let mod_a = d.lemma(p.bit_mod_two, &[a, m]);
    let mod_b = d.lemma(p.bit_mod_two, &[b, n]);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);

    let bitval1_bool = d.beq(cond_a, one);
    let bitval1 = {
        let combined = d.apply(f_expr, &[bitval1_bool, mod_bn_bool]);
        d.bool_select_nat(combined, one, zero)
    };
    let bitval0_to_1 = d.congr(mod_am, cond_a, mod_a, &|d, x| {
        let one = d.num(1);
        let zero = d.zero();
        let x_bool = d.beq(x, one);
        let combined = d.apply(f_expr, &[x_bool, mod_bn_bool]);
        d.bool_select_nat(combined, one, zero)
    });

    let bitval2_bool = d.beq(cond_b, one);
    let bitval2 = {
        let combined = d.apply(f_expr, &[bitval1_bool, bitval2_bool]);
        d.bool_select_nat(combined, one, zero)
    };
    let bitval1_to_2 = d.congr(mod_bn, cond_b, mod_b, &|d, x| {
        let one = d.num(1);
        let zero = d.zero();
        let x_bool = d.beq(x, one);
        let combined = d.apply(f_expr, &[bitval1_bool, x_bool]);
        d.bool_select_nat(combined, one, zero)
    });

    let h_a = cond_beq_one_eq_self(d, &p, a);
    let bitval3 = {
        let combined = d.apply(f_expr, &[a, bitval2_bool]);
        d.bool_select_nat(combined, one, zero)
    };
    let bitval2_to_3 = congr_bool_to_nat(d, bitval1_bool, a, h_a, &|d, hole| {
        let one = d.num(1);
        let zero = d.zero();
        let combined = d.apply(f_expr, &[hole, bitval2_bool]);
        d.bool_select_nat(combined, one, zero)
    });

    let h_b = cond_beq_one_eq_self(d, &p, b);
    let bitval4 = bitwise_bit_combine(d, f_expr, a, b);
    let bitval3_to_4 = congr_bool_to_nat(d, bitval2_bool, b, h_b, &|d, hole| {
        let one = d.num(1);
        let zero = d.zero();
        let combined = d.apply(f_expr, &[a, hole]);
        d.bool_select_nat(combined, one, zero)
    });

    let (_bitval_final, bitval_chain) = d.chain(
        bitval0,
        &[
            (bitval1, bitval0_to_1),
            (bitval2, bitval1_to_2),
            (bitval3, bitval2_to_3),
            (bitval4, bitval3_to_4),
        ],
    );

    let guarded_mid = guarded(
        d, bit_am, bit_bn, on_n_zero0, on_m_zero0, bitwise_mn, bitval0,
    );
    let guarded_final = guarded(
        d, bit_am, bit_bn, on_n_zero0, on_m_zero0, bitwise_mn, bitval4,
    );
    let step_rec = d.congr(rec0, bitwise_mn, rec_chain, &|d, hole| {
        guarded(d, bit_am, bit_bn, on_n_zero0, on_m_zero0, hole, bitval0)
    });
    let step_bit = d.congr(bitval0, bitval4, bitval_chain, &|d, hole| {
        guarded(d, bit_am, bit_bn, on_n_zero0, on_m_zero0, bitwise_mn, hole)
    });

    // --- resolve the two guards ---------------------------------------------
    let step_guard = resolve_bitwise_bit_guard(d, &p, f_expr, hm, hn, a, m, b, n, bitwise_mn);

    let fab = d.apply(f_expr, &[a, b]);
    let target = d.const_app(p.bit, &[fab, bitwise_mn]);

    let (_final, proof) = d.chain(
        bitwise_ab,
        &[
            (aux_fuel, step0),
            (guarded0, step1),
            (guarded_mid, step_rec),
            (guarded_final, step_bit),
            (target, step_guard),
        ],
    );

    let stmt = d.eq(bitwise_ab, target);

    let ty = {
        let with_hn = d.arrow(hn_ty, stmt);
        let with_hm = d.arrow(hm_ty, with_hn);
        let with_n = d.pi_fv(n_fv, nat, with_hm);
        let with_b = d.pi_fv(b_fv, bool_ty, with_n);
        let with_m = d.pi_fv(m_fv, nat, with_b);
        let with_a = d.pi_fv(a_fv, bool_ty, with_m);
        d.pi_fv(f_fv, f_ty, with_a)
    };
    let value = {
        let with_hn = d.lam_fv(hn_fv, hn_ty, proof);
        let with_hm = d.lam_fv(hm_fv, hm_ty, with_hn);
        let with_n = d.lam_fv(n_fv, nat, with_hm);
        let with_b = d.lam_fv(b_fv, bool_ty, with_n);
        let with_m = d.lam_fv(m_fv, nat, with_b);
        let with_a = d.lam_fv(a_fv, bool_ty, with_m);
        d.lam_fv(f_fv, f_ty, with_a)
    };
    d.declare_theorem(p.bitwise_bit, ty, value)
}
