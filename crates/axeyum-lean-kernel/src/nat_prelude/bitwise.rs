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
//! which this file does not attempt to reconstruct (see the module-level
//! doc in `nat_prelude.rs`'s bitwise section for why a full
//! `∀ m n, bitwise f m n = <sibling> m n` equivalence proof was scoped out).
//!
//! # What was NOT attempted, and why
//!
//! A full universal equivalence `∀ m n, bitwise and m n = land m n` was
//! **not** proved. `bitwiseAux`'s per-bit step and `landAux`'s per-bit step
//! are different formulas (`bool_select_nat (and (beq a 1) (beq b 1)) 1 0`
//! vs. `mul a b`) that agree at every *concrete* `a, b ∈ {0, 1}` but are not
//! definitionally equal at *symbolic* `a, b` (`Nat.mul` does not reduce
//! against an unresolved `Nat.mod` term). Closing that gap needs an
//! induction relating two independently-built `Nat.rec` instances plus a
//! `Nat.mod _ 2 ∈ {0, 1}` case-split lemma this prelude does not yet carry —
//! real proof engineering, sized past this lane's scope. What this file
//! proves instead, as the strongest available check without that induction,
//! is **concrete-instance equality against the actual sibling
//! declarations**: [`bitwise_and_eq_land_three_five`] and
//! [`bitwise_or_eq_lor_three_five`] state `Eq (bitwise and_fn 3 5) (land 3
//! 5)` / `… (lor 3 5)` and close by `refl` — both sides fully compute to the
//! same literal numeral, so this is a genuine (if non-universal) admission
//! that the general definition specializes correctly at a witness where
//! `land`/`lor`'s own sanity checks already discriminate a wrong-way step.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
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
/// select `Nat` values.
fn bool_select_bool(d: &mut NatDev<'_>, condition: ExprId, on_true: ExprId, on_false: ExprId) -> ExprId {
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
/// `bitwise`'s `f` slot for the evaluation tests below.
fn and_fn(d: &mut NatDev<'_>) -> ExprId {
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
fn or_fn(d: &mut NatDev<'_>) -> ExprId {
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
fn xor_fn(d: &mut NatDev<'_>) -> ExprId {
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
