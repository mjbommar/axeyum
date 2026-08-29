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
use super::ops::{
    NatDev, NatOps, agree_by_double_fuel_induction, agree_by_fuel_induction, cases_zero_succ,
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

/// `Eq.{1} Bool x y` — the `Bool`-sorted twin of [`NatOps::eq`] (hardcoded to
/// `Nat`). Needed because `hf`'s conclusion, and the intermediate swap steps
/// built from it, are `Bool` equalities, not `Nat` ones.
fn bool_eq(d: &mut NatDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let one = d.level_one();
    let eq_name = d.prelude().logic.eq;
    let eq = d.kernel().const_(eq_name, vec![one]);
    let bool_ty = d.bool_ty();
    d.apply(eq, &[bool_ty, x, y])
}

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)` — the `Bool`-scrutinee twin of
/// [`NatOps::congr`] (whose `eq_motive` is hardcoded to bind its `Eq.rec`
/// motive variable at `Nat`, so it cannot express a hypothesis about a
/// `Bool` equality). Built manually rather than widening `ops.rs`'s generic
/// `congr`, since this is the only site in the whole prelude needing a
/// congruence *hypothesis* over `Bool` — every other `Bool`-valued
/// congruence in this file (`bit_agreement`, `lor_bit_comm`) closes by case
/// split on a concrete `f`, never by transporting an abstract equality.
fn congr_bool_to_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let fa = f(d, a);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let fx = f(d, x);
    let concl = d.eq(fa, fx);
    let eq_bool_ax = bool_eq(d, a, x);
    let anon = d.anon_name();
    let inner_lam = d.kernel().lam(anon, eq_bool_ax, concl, BinderInfo::Default);
    let motive = d.lam_fv(x_fv, bool_ty, inner_lam);
    let refl_case = d.refl(fa);
    let z = d.kernel().level_zero();
    let one = d.level_one();
    let eq_rec_name = d.prelude().logic.eq_rec;
    let eq_rec = d.kernel().const_(eq_rec_name, vec![z, one]);
    d.apply(eq_rec, &[bool_ty, a, motive, refl_case, b, h])
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
fn bitwise_bit_comm(d: &mut NatDev<'_>, f_expr: ExprId, hf_expr: ExprId, m: ExprId, n: ExprId) -> ExprId {
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
    theorem_with_f(d, p.bitwise_aux_zero_left_any_fuel, 2, &|d, f_expr, values| {
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
    })?;
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
fn declare_bitwise_aux_agree_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
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
        let (_, right_is_target) =
            d.chain(right_term, &[(right_at_zero, right_congr), (target, any_fuel)]);
        let right_is_target_rev = d.symm(right_term, target, right_is_target);

        let body = d.trans(left_term, target, right_term, left_is_target, right_is_target_rev);
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
                let body =
                    d.trans(left_term, target, right_term, left_is_target, right_is_target_rev);

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

                let start = guarded(d, succ_pred, n, on_n_zero, on_m_zero, recursive_general, bit_general);
                let mid = guarded(d, succ_pred, n, on_n_zero, on_m_zero, recursive_at_f2p, bit_general);
                let inner_step = d.congr(recursive_general, recursive_at_f2p, ih_at_half, &|d, hole| {
                    guarded(d, succ_pred, n, on_n_zero, on_m_zero, hole, bit_general)
                });

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
        let concl = bool_eq(d, fab, fba);
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

        let lhs_congr =
            d.congr(b, zero, b_eq_zero, &|d, x| d.bool_select_nat(f_false_true, x, zero));
        let rhs_congr =
            d.congr(a, zero, a_eq_zero, &|d, x| d.bool_select_nat(f_false_true, x, zero));
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
        let concl = bool_eq(d, fab, fba);
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
