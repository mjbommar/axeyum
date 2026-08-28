//! `Nat.clog` — the ceiling base-`b` logarithm, by the same **fuel**
//! technique [`log.rs`](super::log) uses for `Nat.log`.
//!
//! Mathlib v4.30 defines
//!
//! ```text
//! def Nat.clog (b : ℕ) : ℕ → ℕ
//!   | n => if h : 1 < b ∧ 1 < n then clog b ((n + b - 1) / b) + 1 else 0
//! ```
//!
//! which is structurally the same shape as `Nat.log` — a non-structural
//! recursive call, guarded by a two-part condition — with two differences:
//! the second guard conjunct is `1 < n` rather than `b ≤ n`, and the
//! recursive argument is `(n + b - 1) / b` (the ceiling of `n / b`) rather
//! than the plain floor `n / b`. Neither difference touches the fuel
//! construction itself: `clog` recurses structurally on a fuel argument
//! exactly as `log` does, instantiated at `n` itself, and both equations
//! hold **definitionally** (β/δ/ι), so nothing here appeals to an axiom.
//!
//! ```text
//! Nat.clogAux b 0        n ≡ 0
//! Nat.clogAux b (succ f) n ≡ if 2 ≤ b then (if 2 ≤ n then succ (clogAux b f ((n + b - 1) / b)) else 0) else 0
//! Nat.clog b n           := Nat.clogAux b n n
//! ```
//!
//! `(n + b - 1)` uses [`NatOps::sub`](super::ops::NatOps::sub), which
//! truncates (`3 - 5 = 0`). That never bites here: the subtrahend is the
//! literal `1`, and `n + b ≥ 1` for any `n, b` with `n + b` reachable from a
//! `succ`, so `n + b - 1` never truncates on the branch that is actually
//! selected. The four boundary theorems below never need the quotient's
//! *value* at all — each one collapses through the guard before the
//! recursive call is ever forced — so the subtraction's behaviour on
//! degenerate operands is moot for this file.
//!
//! **Guard nesting, and why it is the OPPOSITE of `log.rs`'s.** `log`'s
//! guard mixed a `b`-only cut (`2 ≤ b`) with a cut relating `b` and `n`
//! (`b ≤ n`), and put the mixed cut outermost because `log_of_lt` needed it
//! there. `clog`'s guard is `2 ≤ b ∧ 2 ≤ n` — **both cuts are single-variable**
//! — and the four theorems this file proves split cleanly along that line:
//! `clog_zero_left`/`clog_one_left` fix `b` and vary `n`, so they need the
//! `b`-only cut (`2 ≤ b`) OUTERMOST to collapse in one rewrite regardless of
//! `n`; `clog_zero_right` never reaches the guard at all (fuel `0`);
//! `clog_one_right` fixes `n = 1`, so its `n`-only cut (`2 ≤ n`, i.e. `2 ≤
//! 1`) is a closed `false` no matter which branch of a case split on `b` it
//! is reached from. So `2 ≤ b` outermost serves every theorem this file
//! proves; there is no tension to resolve by ordering, unlike `log`'s mixed
//! cuts.
//!
//! Only the four boundary equations land here (`clog_zero_left`,
//! `clog_zero_right`, `clog_one_left`, `clog_one_right`). `clog_pos` and
//! `log_le_clog` need `clogAux b f n ≤ f`-style motives generalized over the
//! fuel — a real induction, not a case split — and are a separate task.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.clogAux base fuel value`.
fn clog_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    fuel: ExprId,
    value: ExprId,
) -> ExprId {
    d.const_app(p.clog_aux, &[base, fuel, value])
}

/// `Nat.clog base value`.
fn clog(d: &mut NatDev<'_>, p: &NatPrelude, base: ExprId, value: ExprId) -> ExprId {
    d.const_app(p.clog, &[base, value])
}

/// Declare `Nat.clogAux`, `Nat.clog`, and the four boundary equations that
/// fall out of the guard by ι-reduction alone.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_clog_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let level_one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);

    // --- Nat.clogAux : Nat -> Nat -> Nat -> Nat -----------------------------
    {
        let base_fv = d.fresh_fvar();
        let base = d.kernel().fvar(base_fv);
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);

        // fuel = zero: the constant-zero row.
        let zero_minor = {
            let unused_fv = d.fresh_fvar();
            let zero = d.zero();
            d.lam_fv(unused_fv, nat, zero)
        };

        // fuel = succ f: guard on `2 <= base` OUTERMOST, then on `2 <=
        // argument`. See the module doc for why this order (the reverse of
        // `log.rs`'s) is the one every theorem here needs.
        let succ_minor = {
            let predecessor_fv = d.fresh_fvar();
            let row_fv = d.fresh_fvar();
            let row = d.kernel().fvar(row_fv);
            let argument_fv = d.fresh_fvar();
            let argument = d.kernel().fvar(argument_fv);
            let one = d.num(1);
            let sum = d.add(argument, base);
            let numerator = d.sub(sum, one);
            let quotient = d.div(numerator, base);
            let recursive = d.apply(row, &[quotient]);
            let stepped = d.succ(recursive);
            let zero = d.zero();
            let two = d.num(2);
            let value_exceeds_one = d.ble(two, argument);
            let inner = d.bool_select_nat(value_exceeds_one, stepped, zero);
            let base_exceeds_one = d.ble(two, base);
            let body = d.bool_select_nat(base_exceeds_one, inner, zero);
            let with_argument = d.lam_fv(argument_fv, nat, body);
            let with_row = d.lam_fv(row_fv, nat_to_nat, with_argument);
            d.lam_fv(predecessor_fv, nat, with_row)
        };

        let motive = d.kernel().lam(anon, nat, nat_to_nat, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![level_one]);
        let row = d.apply(rec, &[motive, zero_minor, succ_minor, fuel]);
        let applied = d.apply(row, &[value]);
        let value_term = {
            let with_value = d.lam_fv(value_fv, nat, applied);
            let with_fuel = d.lam_fv(fuel_fv, nat, with_value);
            d.lam_fv(base_fv, nat, with_fuel)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            let middle = d.arrow(nat, inner);
            d.arrow(nat, middle)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.clog_aux,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.clog b n := Nat.clogAux b n n ----------------------------------
    {
        let base_fv = d.fresh_fvar();
        let base = d.kernel().fvar(base_fv);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let body = clog_aux(d, &p, base, value, value);
        let value_term = {
            let with_value = d.lam_fv(value_fv, nat, body);
            d.lam_fv(base_fv, nat, with_value)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.clog,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // clog b 0 = 0 -- the fuel is already exhausted (fuel = value = 0), so
    // this is pure iota, no induction needed (`Mathlib`: `Nat.clog_zero_right`).
    d.theorem(p.clog_zero_right, 1, &|d, values| {
        let base = values[0];
        let zero = d.zero();
        let lhs = clog(d, &p, base, zero);
        (d.eq(lhs, zero), d.refl(lhs))
    })?;

    // clog 0 n = 0 -- `ble 2 0` is `false`, so the outer cut collapses in
    // every fuel case regardless of `n`. The induction on `n` only exposes
    // the fuel's constructor; the induction hypothesis is never used
    // (`Mathlib`: `Nat.clog_zero_left`).
    d.theorem(p.clog_zero_left, 1, &|d, values| {
        let value = values[0];
        let zero = d.zero();
        let lhs = clog(d, &p, zero, value);
        let stmt = d.eq(lhs, zero);
        let proof = d.induct(
            &|d, candidate| {
                let zero = d.zero();
                let lhs = clog(d, &p, zero, candidate);
                d.eq(lhs, zero)
            },
            &|d| {
                let zero = d.zero();
                let lhs = clog(d, &p, zero, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let zero = d.zero();
                let candidate = d.succ(predecessor);
                let lhs = clog(d, &p, zero, candidate);
                d.refl(lhs)
            },
            value,
        );
        (stmt, proof)
    })?;

    // clog 1 n = 0 -- `ble 2 1` reduces to `ble 1 0`, i.e. `false`
    // (`Mathlib`: `Nat.clog_one_left`).
    d.theorem(p.clog_one_left, 1, &|d, values| {
        let value = values[0];
        let zero = d.zero();
        let one = d.num(1);
        let lhs = clog(d, &p, one, value);
        let stmt = d.eq(lhs, zero);
        let proof = d.induct(
            &|d, candidate| {
                let zero = d.zero();
                let one = d.num(1);
                let lhs = clog(d, &p, one, candidate);
                d.eq(lhs, zero)
            },
            &|d| {
                let zero = d.zero();
                let one = d.num(1);
                let lhs = clog(d, &p, one, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let one = d.num(1);
                let candidate = d.succ(predecessor);
                let lhs = clog(d, &p, one, candidate);
                d.refl(lhs)
            },
            value,
        );
        (stmt, proof)
    })?;

    // clog b 1 = 0 -- a THREE-way case analysis on `b`: `b = 0` and `b = 1`
    // fail `2 <= b`, and `b = succ (succ k)` passes it but then hits the
    // INNER cut `2 <= 1`, which is a closed `false` no matter what `k` is
    // (`Mathlib`: `Nat.clog_one_right`).
    d.theorem(p.clog_one_right, 1, &|d, values| {
        let base = values[0];
        let zero = d.zero();
        let one = d.num(1);
        let lhs = clog(d, &p, base, one);
        let stmt = d.eq(lhs, zero);
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| {
            let zero = d.zero();
            let one = d.num(1);
            let lhs = clog(d, &p, candidate, one);
            d.eq(lhs, zero)
        };
        let refl_at = |d: &mut NatDev<'_>, candidate: ExprId| {
            let one = d.num(1);
            let lhs = clog(d, &p, candidate, one);
            d.refl(lhs)
        };
        let proof = d.induct(
            &statement_at,
            &|d| {
                let zero = d.zero();
                refl_at(d, zero)
            },
            &|d, predecessor, _ih| {
                d.induct(
                    &|d, inner| {
                        let candidate = d.succ(inner);
                        statement_at(d, candidate)
                    },
                    &|d| {
                        let one = d.num(1);
                        refl_at(d, one)
                    },
                    &|d, inner, _inner_ih| {
                        let candidate = d.succ(inner);
                        let candidate = d.succ(candidate);
                        refl_at(d, candidate)
                    },
                    predecessor,
                )
            },
            base,
        );
        (stmt, proof)
    })?;

    Ok(())
}
