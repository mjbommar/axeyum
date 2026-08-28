//! `Nat.ldiff` — bitwise "AND NOT" (`m` with every bit `n` sets cleared), by
//! the same **structural fuel recursion** device [`land`](super::land) and
//! [`lor`](super::lor) use for `Nat.land`/`Nat.lor`.
//!
//! Mathlib v4.30 (`Mathlib.Data.Nat.Bitwise`) defines `Nat.ldiff` the same
//! way it defines `Nat.land`/`Nat.lor` — through the general two-argument
//! `Nat.bitwise`, which recurses on neither argument structurally and needs
//! well-founded recursion through the equation compiler. `land.rs`'s module
//! doc explains why that is out of scope for a single lane; this lane lands
//! `Nat.ldiff` directly rather than through `Nat.bitwise`, same as its two
//! siblings.
//!
//! **`Nat.ldiff` has an absorbing zero on exactly ONE side, and working out
//! which side drives every choice below.** `ldiff 0 n = 0` (`0` has no bits
//! to keep, so ANDing with anything clears everything) but `ldiff m 0 = m`
//! (`NOT 0` is all-ones, so ANDing with it changes nothing) — the absorbing
//! zero is on the **left**, the `m` side, not the right. That matters
//! because `land`/`lor` both size their fuel as `landAux/lorAux m m n`: the
//! **same** operand (`m`) supplies both the fuel budget and the value that
//! gets halved down to structural `0` first. Whichever operand that is
//! determines what the fuel-exhaustion row is allowed to return —
//! `land.rs` and `lor.rs` both establish that by the time the fuel `Nat.rec`
//! actually reaches its zero case, the **current `m`-argument at that call
//! is always definitionally `0`** (fuel decrements by `1` per step while the
//! `m`-argument at least halves per step, and halving a value `m` times
//! always reaches `0` in at most `m` halvings for `m ≥ 1`), regardless of
//! what the `n`-argument is at that point.
//!
//! For `land`, that operand (`m`) carries an absorbing zero, so the
//! fuel-exhaustion row can safely ignore both arguments and return the
//! constant `0` — `land 0 n = 0` for every `n`, including whatever `n` is
//! left unconsumed. For `lor`, `m` carries **no** absorbing zero, so a
//! constant-`0` row is wrong whenever fuel runs out with real bits of `n`
//! still unconsumed (measured directly: `lorAux` reached with fuel `= 1`,
//! `m = 1`, `n = 100000` hits its zero-fuel row at `m`-argument `0`,
//! `n`-argument `50000` — a constant-`0` row would silently drop all of
//! `n`'s high bits); `lor.rs` fixes this by returning the row's own
//! `n`-argument instead.
//!
//! **`Nat.ldiff` sizes its fuel the same way (`ldiffAux m m n`), and `m` is
//! exactly the side that carries the absorbing zero — so `land`'s
//! fuel-exhaustion shape transfers unchanged: return the constant `0`,
//! ignoring both arguments.** By the invariant above, the `m`-argument at
//! that call is always `0`, and `ldiff 0 n = 0` for every `n`, so ignoring
//! the leftover `n`-argument is exactly as safe as it is for `land` — and
//! for the identical reason (the fuel-sized operand IS the absorbing-zero
//! operand), not merely by analogy.
//!
//! That settles the OUTER (`Nat.rec`-on-fuel) base case. The INNER guard
//! inside the successor row is a genuine hybrid of both siblings, because
//! the two zero-checks protect two *different* operands with *different*
//! absorbing behaviour:
//!
//! - `n = 0`: `ldiff m 0 = m` — no absorbing zero on this side, so the
//!   guard must return the row's **current `m`-argument unchanged** (a
//!   pass-through), exactly `lor`'s `n = 0` branch shape (which also
//!   returns `m`, for the unrelated reason that `0` is `lor`'s identity
//!   element on that side).
//! - `m = 0`: `ldiff 0 n = 0` — absorbing zero, so the guard returns the
//!   constant `0`, exactly `land`'s `m = 0` branch shape.
//!
//! Per-bit, the combining step is neither the product `land` uses (AND of
//! two `{0,1}` values) nor the `max` `lor` uses (via `Nat.ble` +
//! `bool_select_nat`) — `ldiff`'s per-bit rule is "keep `m`'s bit unless
//! `n`'s bit is set": `bitLdiff a b := if b = 0 then a else 0`. This reuses
//! only primitives already load-bearing in this same term (`Nat.beq` against
//! the literal `0`, `bool_select_nat`) — the same combinator the zero-guards
//! already call, so no new primitive or height dependency is added beyond
//! what `land`/`lor` already need from `Nat.div`/`Nat.mod`.
//!
//! ```text
//! Nat.ldiffAux 0        m n ≡ 0
//! Nat.ldiffAux (succ f) m n ≡
//!   if n = 0 then m
//!   else if m = 0 then 0
//!   else 2 * ldiffAux f (m/2) (n/2) + (if (n%2) = 0 then (m%2) else 0)
//! Nat.ldiff m n := Nat.ldiffAux m m n
//! ```
//!
//! **The guard's nesting order is UNCHANGED from `land.rs`/`lor.rs` — `n = 0`
//! OUTERMOST — for the identical proof-cost reason.** `Nat.ldiff 0 n = 0`
//! ([`ldiff_zero_left`](NatPrelude::ldiff_zero_left)) is `refl`: fuel is
//! `m = 0`, so the outer `Nat.rec` is already exhausted and hits the
//! constant-`0` base case directly, never touching the inner guards at all.
//! `Nat.ldiff m 0 = m`
//! ([`ldiff_zero_right`](NatPrelude::ldiff_zero_right)) is not `refl` at
//! symbolic `m` (the outer fuel-`Nat.rec` is stuck until `m`'s constructor
//! shape is exposed), so it needs induction on `m` — but with `n = 0` tested
//! first at every step, `beq n 0` reduces to `true` by delta+iota alone
//! (`n` is the theorem's own literal `Nat.zero`), so the outer
//! `bool_select_nat` selects the "return `m`" branch immediately without
//! forcing the untaken branch (which is where the `m = 0` test and the
//! actual recursive call live) — every induction step collapses to `refl`,
//! the induction hypothesis unused, exactly `land_zero_right`'s /
//! `lor_zero_right`'s shape.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.ldiffAux fuel m n`.
fn ldiff_aux(d: &mut NatDev<'_>, p: &NatPrelude, fuel: ExprId, m: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.ldiff_aux, &[fuel, m, n])
}

/// `Nat.ldiff m n`.
fn ldiff(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.ldiff, &[m, n])
}

/// Declare `Nat.ldiffAux`, `Nat.ldiff`, and four boundary/sanity theorems.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_ldiff_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);
    // The Nat.rec row type once the fuel argument has been consumed: a
    // function of the two remaining arguments `m` and `n`.
    let row_ty = d.arrow(nat, nat_to_nat);

    // --- Nat.ldiffAux : Nat -> Nat -> Nat -> Nat ----------------------------
    {
        // fuel = zero: constant-zero row, regardless of m, n -- see the
        // module doc: `m` is both the fuel and the absorbing-zero operand,
        // so by the time fuel is exhausted the current `m`-argument is
        // already definitionally 0, and `ldiff 0 n = 0` for every n.
        let zero_minor = {
            let m_fv = d.fresh_fvar();
            let n_fv = d.fresh_fvar();
            let zero = d.zero();
            let with_n = d.lam_fv(n_fv, nat, zero);
            d.lam_fv(m_fv, nat, with_n)
        };

        // fuel = succ predecessor: guard on `n = 0` OUTERMOST (returning
        // `m` unchanged -- ldiff m 0 = m, no absorbing zero on this side),
        // then `m = 0` (returning `0` -- the absorbing-zero side) -- see the
        // module doc for why the order is load-bearing. The real
        // ldiff-at-this-bit step is
        // `2 * row(m/2, n/2) + (if (n%2) = 0 then (m%2) else 0)`, where
        // `row` is the recursive call at the smaller fuel and the per-bit
        // combination reuses `beq`/`bool_select_nat`, already load-bearing
        // in this same term for the zero-guards.
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
            let bit_n_is_zero = d.beq(bit_n, zero);
            let bit_ldiff = d.bool_select_nat(bit_n_is_zero, bit_m, zero);
            let stepped = d.add(doubled, bit_ldiff);

            let m_is_zero = d.beq(m, zero);
            let inner = d.bool_select_nat(m_is_zero, zero, stepped);
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
            name: p.ldiff_aux,
            uparams: vec![],
            // Strictly greater than the height of everything it calls
            // (`Nat.div`/`Nat.mod` are height 3, `Nat.mul`/`Nat.beq` are
            // lower still) -- matches `landAux`/`lorAux`'s choice for the
            // identical call-graph shape.
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.ldiff m n := Nat.ldiffAux m m n --------------------------------
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = ldiff_aux(d, &p, m, m, n);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(m_fv, nat, with_n)
        };
        let ty = d.arrow(nat, nat_to_nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.ldiff,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // ldiff_zero_left : ∀ n, Eq (ldiff 0 n) 0 -- refl: fuel = m = 0 exhausts
    // the outer Nat.rec immediately, regardless of n. See module doc.
    d.theorem(p.ldiff_zero_left, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();
        let lhs = ldiff(d, &p, zero, n);
        (d.eq(lhs, zero), d.refl(lhs))
    })?;

    // ldiff_zero_right : ∀ m, Eq (ldiff m 0) m -- induction on m to expose
    // the fuel's constructor; base and step are both `refl`, no induction
    // hypothesis used, because the `n = 0` guard (tested outermost)
    // collapses the whole succ-step term to `m` regardless of the fuel
    // predecessor -- exactly `lor_zero_right`'s shape. See module doc.
    d.theorem(p.ldiff_zero_right, 1, &|d, values| {
        let m = values[0];
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| {
            let zero = d.zero();
            let lhs = ldiff(d, &p, candidate, zero);
            d.eq(lhs, candidate)
        };
        let proof = d.induct(
            &statement_at,
            &|d| {
                let zero = d.zero();
                let lhs = ldiff(d, &p, zero, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let candidate = d.succ(predecessor);
                let zero = d.zero();
                let lhs = ldiff(d, &p, candidate, zero);
                d.refl(lhs)
            },
            m,
        );
        let stmt = statement_at(d, m);
        (stmt, proof)
    })?;

    // ldiff_three_five : Eq (ldiff 3 5) 2 -- 011 &~ 101 = 010. Two fuel
    // steps with genuinely differing bit patterns, so this is the sanity
    // check that would catch a wrong-way `bit_ldiff` (e.g. an AND-shaped or
    // OR-shaped step) that a diagonal case alone cannot distinguish.
    d.theorem(p.ldiff_three_five, 0, &|d, _values| {
        let three = d.num(3);
        let five = d.num(5);
        let two = d.num(2);
        let lhs = ldiff(d, &p, three, five);
        (d.eq(lhs, two), d.refl(lhs))
    })?;

    // ldiff_five_three : Eq (ldiff 5 3) 4 -- 101 &~ 011 = 100. The
    // asymmetry check: `ldiff` is NOT commutative, unlike `land`/`lor`, so
    // swapping the same two operands must produce a DIFFERENT result
    // (`4`, not `2`) -- the sharpest negative control available for this
    // definition, and one `land`/`lor` cannot even express.
    d.theorem(p.ldiff_five_three, 0, &|d, _values| {
        let three = d.num(3);
        let five = d.num(5);
        let four = d.num(4);
        let lhs = ldiff(d, &p, five, three);
        (d.eq(lhs, four), d.refl(lhs))
    })?;

    Ok(())
}
