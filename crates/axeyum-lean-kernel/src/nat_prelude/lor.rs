//! `Nat.lor` — bitwise OR, by the same **structural fuel recursion** device
//! [`land`](super::land) uses for `Nat.land`, [`log`](super::log) uses for
//! `Nat.log`, and [`binary`](super::binary) uses for
//! `Nat.testBit`/`Nat.size`.
//!
//! Mathlib v4.30 (`Mathlib.Data.Nat.Bitwise`) defines `Nat.lor` the same way
//! it defines `Nat.land` — through the general two-argument `Nat.bitwise`,
//! which recurses on neither argument structurally and needs well-founded
//! recursion through the equation compiler. `land.rs`'s module doc explains
//! why that is out of scope for a single lane; the same reasoning applies
//! here, and this lane lands `Nat.lor` directly rather than through
//! `Nat.bitwise`.
//!
//! **`land.rs`'s per-bit shortcut does NOT transfer, and the reason is worth
//! stating precisely.** `land` picks each bit's AND as the `Nat` **product**
//! of two values already in `{0, 1}`. OR of two such values is NOT their
//! product — `1 + 1 - 1*1`, `max 1 1`, and a `Bool.rec` case split all give
//! the right answer (`1`), and this file picks **`max` via the existing
//! `Nat.ble` + the shared `bool_select_nat` combinator** (`if a ≤ b then b
//! else a`), because:
//!
//! - `ble` is already the cheapest boolean primitive in this prelude
//!   (`ReducibilityHint::Regular(1)`, the same height as `beq`, which this
//!   very declaration already calls for its zero-guards) — so `max` adds no
//!   new height dependency beyond what the fuel recursion already needs from
//!   `Nat.div`/`Nat.mod` (height 3).
//! - `a + b - a*b` would additionally route through `Nat.sub`, which
//!   truncates silently. It is *safe* here (bit values never make `a*b > a+b`
//!   in this domain), but it is one more definition on the call graph and one
//!   more thing a reader must confirm never triggers truncation, for no
//!   payoff — `bool_select_nat` is already load-bearing in this same term for
//!   the zero-guards, so reusing it for the per-bit step adds nothing new.
//! - A bespoke `Bool.rec` cut (mirroring [`bits`](super::bits)'s `Nat.bit`)
//!   would need its own `Bool → Bool → Bool` OR combinator and a `Nat`-side
//!   encode/decode around it — strictly more construction than `max` for the
//!   same result.
//!
//! **The fuel bound itself does NOT transfer unchanged, and this is the part
//! that actually needed working out.** `land m n := landAux m m n` uses `m`
//! alone as fuel, which is sound for AND only because AND has an absorbing
//! zero: once `m`'s (halved) value hits `0`, the result is `0` regardless of
//! how much of `n` is left unconsumed, so a fuel budget that only accounts
//! for `m`'s magnitude is enough. OR has no such absorbing element on either
//! side — `0 lor n = n`, not `0` — so if the fuel budget were sized only to
//! exhaust `m` and `m` is small while `n` is large, the naive translation
//! would silently drop `n`'s high bits.
//!
//! The fix is not a bigger fuel budget (`m + n`, say) but a corrected base
//! case: **`lorAux`'s fuel-exhaustion row returns `n` instead of the constant
//! `0`.** This is sound with fuel `= m` unchanged, because whenever the
//! *outer* `Nat.rec` on fuel actually reaches `0`, the `m`-argument at that
//! point has *already* been halved down to `0` too — fuel ticks down by
//! exactly `1` per step while the halved `m`-argument shrinks by a factor of
//! `2` per step, and `m` itself (the starting fuel) is always at least
//! `⌊log₂ m⌋ + 1`, the number of halvings needed to exhaust it — so the
//! per-step guards below (which check the *current*, already-halved operand,
//! not the fuel counter) always fire first, well inside the fuel budget, and
//! the raw fuel-exhaustion base case is only ever reached with a
//! *definitionally* zero `m`-argument. At that point `0 lor n = n` is exactly
//! what returning `n` computes, and it holds even when `n` is symbolic —
//! `lor_zero_left` below is `refl` for exactly this reason, the same shape as
//! `land_zero_left`.
//!
//! ```text
//! Nat.lorAux 0        m n ≡ n
//! Nat.lorAux (succ f) m n ≡
//!   if n = 0 then m
//!   else if m = 0 then n
//!   else 2 * lorAux f (m / 2) (n / 2) + max (m % 2) (n % 2)
//! Nat.lor m n := Nat.lorAux m m n
//! ```
//!
//! **The guard's nesting order is UNCHANGED from `land.rs` — `n = 0`
//! OUTERMOST — and it is load-bearing for exactly the same proof-cost
//! reason.** `Nat.lor 0 n = n` ([`lor_zero_left`](NatPrelude::lor_zero_left))
//! is `refl`: fuel is `m = 0`, so the outer `Nat.rec` is already exhausted
//! and hits the corrected base case above, which computes `n` directly by
//! beta alone. `Nat.lor m 0 = m`
//! ([`lor_zero_right`](NatPrelude::lor_zero_right)) is not `refl` at
//! symbolic `m` (the outer fuel-`Nat.rec` is stuck until `m`'s constructor
//! shape is exposed), so it needs induction on `m` — but with `n = 0` tested
//! first at every step, `beq n 0` reduces to `true` by delta+iota alone
//! (`n` is the theorem's own literal `Nat.zero`), so the *outer*
//! `bool_select_nat` selects the "return `m`" branch immediately without
//! forcing the untaken branch (which is where the actual recursive call and
//! the `Nat.div`/`Nat.mod` unfolding would live) — every induction step
//! collapses to `refl`, the induction hypothesis unused, exactly
//! `land_zero_right`'s shape.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.lorAux fuel m n`.
fn lor_aux(d: &mut NatDev<'_>, p: &NatPrelude, fuel: ExprId, m: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.lor_aux, &[fuel, m, n])
}

/// `Nat.lor m n`.
fn lor(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.lor, &[m, n])
}

/// Declare `Nat.lorAux`, `Nat.lor`, and three boundary/sanity theorems.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_lor_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);
    // The Nat.rec row type once the fuel argument has been consumed: a
    // function of the two remaining arguments `m` and `n`.
    let row_ty = d.arrow(nat, nat_to_nat);

    // --- Nat.lorAux : Nat -> Nat -> Nat -> Nat ------------------------------
    {
        // fuel = zero: return `n` -- see the module doc for why this (not a
        // constant `0`) is the correct base case for OR, and why it is
        // sound with fuel `= m` unchanged.
        let zero_minor = {
            let m_fv = d.fresh_fvar();
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let with_n = d.lam_fv(n_fv, nat, n);
            d.lam_fv(m_fv, nat, with_n)
        };

        // fuel = succ predecessor: guard on `n = 0` OUTERMOST (returning
        // `m`), then `m = 0` (returning `n`) -- see the module doc for why
        // the order is load-bearing. The real OR-at-this-bit step is
        // `2 * row(m/2, n/2) + max (m%2) (n%2)`, where `row` is the
        // recursive call at the smaller fuel and `max` is built from the
        // existing `Nat.ble` + `bool_select_nat` (no new primitive).
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

            let half_m = d.div(m, two);
            let half_n = d.div(n, two);
            let recursive = d.apply(row, &[half_m, half_n]);
            let doubled = d.mul(two, recursive);
            let bit_m = d.modulo(m, two);
            let bit_n = d.modulo(n, two);
            let bit_m_le_bit_n = d.ble(bit_m, bit_n);
            let bit_or = d.bool_select_nat(bit_m_le_bit_n, bit_n, bit_m);
            let stepped = d.add(doubled, bit_or);

            let m_is_zero = d.beq(m, zero);
            let inner = d.bool_select_nat(m_is_zero, n, stepped);
            let n_is_zero = d.beq(n, zero);
            let body = d.bool_select_nat(n_is_zero, m, inner);

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
            d.lam_fv(fuel_fv, nat, with_m)
        };
        let ty = d.arrow(nat, row_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.lor_aux,
            uparams: vec![],
            // Strictly greater than the height of everything it calls
            // (`Nat.div`/`Nat.mod` are height 3, `Nat.mul`/`Nat.beq`/`Nat.ble`
            // are lower still) -- matches `landAux`'s choice for the
            // identical call-graph shape.
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.lor m n := Nat.lorAux m m n ------------------------------------
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = lor_aux(d, &p, m, m, n);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(m_fv, nat, with_n)
        };
        let ty = d.arrow(nat, nat_to_nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.lor,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // lor_zero_left : ∀ n, Eq (lor 0 n) n -- refl: fuel = m = 0 exhausts the
    // outer Nat.rec immediately, hitting the corrected `n`-returning base
    // case regardless of n's shape. See module doc.
    d.theorem(p.lor_zero_left, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();
        let lhs = lor(d, &p, zero, n);
        (d.eq(lhs, n), d.refl(lhs))
    })?;

    // lor_zero_right : ∀ m, Eq (lor m 0) m -- induction on m to expose the
    // fuel's constructor; base and step are both `refl`, no induction
    // hypothesis used, because the `n = 0` guard (tested outermost)
    // collapses the whole succ-step term to `m` regardless of the fuel
    // predecessor -- exactly `land_zero_right`'s shape. See module doc.
    d.theorem(p.lor_zero_right, 1, &|d, values| {
        let m = values[0];
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| {
            let zero = d.zero();
            let lhs = lor(d, &p, candidate, zero);
            d.eq(lhs, candidate)
        };
        let proof = d.induct(
            &statement_at,
            &|d| {
                let zero = d.zero();
                let lhs = lor(d, &p, zero, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let candidate = d.succ(predecessor);
                let zero = d.zero();
                let lhs = lor(d, &p, candidate, zero);
                d.refl(lhs)
            },
            m,
        );
        let stmt = statement_at(d, m);
        (stmt, proof)
    })?;

    // lor_three_five : Eq (lor 3 5) 7 -- 011 | 101 = 111. Deliberately
    // discriminating from `land_three_five`'s `3 &&& 5 = 1`: a wrong-way
    // `bit_or` (e.g. the AND step reused by mistake, or an OR/AND swap)
    // cannot pass both this and `land_three_five` at once.
    d.theorem(p.lor_three_five, 0, &|d, _values| {
        let three = d.num(3);
        let five = d.num(5);
        let seven = d.num(7);
        let lhs = lor(d, &p, three, five);
        (d.eq(lhs, seven), d.refl(lhs))
    })?;

    Ok(())
}
