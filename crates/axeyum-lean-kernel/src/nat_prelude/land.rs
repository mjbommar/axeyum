//! `Nat.land` — bitwise AND, by **structural fuel recursion** on a bound
//! generous enough to exhaust both operands, the same device
//! [`log`](super::log) uses for `Nat.log` and [`binary`](super::binary) uses
//! for `Nat.testBit`/`Nat.size`.
//!
//! Mathlib v4.30 (`Mathlib.Data.Nat.Bitwise`) defines `Nat.land` via the
//! general two-argument `Nat.bitwise`:
//!
//! ```text
//! def bitwise (f : Bool → Bool → Bool) : Nat → Nat → Nat
//!   | 0,     n     => if f false true  then n else 0
//!   | m + 1, 0     => if f true  false then m + 1 else 0
//!   | m + 1, n + 1 => bit (f (bodd (m+1)) (bodd (n+1)))
//!                         (bitwise f (div2 (m+1)) (div2 (n+1)))
//! def land : Nat → Nat → Nat := bitwise and
//! ```
//!
//! which recurses on neither argument structurally (`div2 (m+1)` is not a
//! constructor predecessor of `m+1`) and needs well-founded recursion —
//! through the equation compiler, `Quot.sound`/`propext`, fatal to this
//! project's axiom-freedom metric, exactly as [`log`](super::log)'s module
//! doc explains for `Nat.log`.
//!
//! **This lane lands `Nat.land` directly rather than the general
//! `Nat.bitwise`.** `Nat.bitwise` needs a `Bool → Bool → Bool` function
//! argument threaded through the mismatched-length base cases above (`f
//! false true` / `f true false`), which is substantially more construction
//! than a single lane's "one definition, landed completely" scope buys.
//! `Nat.land` needs neither: since each bit of `m`/`n` is a `Nat` already in
//! `{0, 1}` (via `Nat.mod _ 2`), their AND at that bit is literally their
//! **product** — `0*0 = 0*1 = 1*0 = 0`, `1*1 = 1` — so the recursive step
//! needs no `Bool`/`cond` combinator at all, unlike `Nat.bit`
//! ([`bits`](super::bits)) or the general `Nat.bitwise`.
//!
//! ```text
//! Nat.landAux 0        m n ≡ 0
//! Nat.landAux (succ f) m n ≡
//!   if n = 0 then 0
//!   else if m = 0 then 0
//!   else 2 * landAux f (m / 2) (n / 2) + (m % 2) * (n % 2)
//! Nat.land m n := Nat.landAux m m n
//! ```
//!
//! `m` itself is the fuel, exactly as `Nat.log b n := Nat.logAux b n n` uses
//! `n` twice: `div2` applied to `m` at most `m` times reaches `0` (in fact in
//! `O(log m)` steps), so `m` iterations are always enough, and once either
//! operand is exhausted every further step just re-selects the `0` branch.
//!
//! **The guard's nesting order is load-bearing, and it is `n = 0`
//! OUTERMOST** — the opposite of which operand a reader might expect to
//! check first, and chosen for the same proof-cost reason `log.rs` puts
//! `b ≤ n` outermost: only the outermost cut collapses the whole succ-step
//! term with a single rewrite, independently of the (possibly still
//! symbolic) fuel predecessor and of `m`. `Nat.land 0 n = 0`
//! ([`land_zero_left`](NatPrelude::land_zero_left)) is `refl` regardless —
//! fuel is `m = 0`, so the OUTER `Nat.rec` on fuel is already exhausted and
//! the guard never even runs. `Nat.land m 0 = 0`
//! ([`land_zero_right`](NatPrelude::land_zero_right)) is not `refl` at
//! symbolic `m` (the outer fuel-`Nat.rec` is stuck until `m`'s constructor
//! shape is exposed), so it needs induction on `m` — but with `n = 0` tested
//! first, every step of that induction is itself `refl`, with the induction
//! hypothesis never used, exactly [`log_zero_left`](super::log)'s shape:
//! `beq n 0` at `n = 0` (a literal `Nat.zero`, from the theorem's own
//! statement) reduces to `true` by delta+iota alone, collapsing the term to
//! `0` no matter what the fuel predecessor or `m` are.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.landAux fuel m n`.
fn land_aux(d: &mut NatDev<'_>, p: &NatPrelude, fuel: ExprId, m: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.land_aux, &[fuel, m, n])
}

/// `Nat.land m n`.
fn land(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.land, &[m, n])
}

/// Declare `Nat.landAux`, `Nat.land`, and four boundary/sanity theorems.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);
    // The Nat.rec row type once the fuel argument has been consumed: a
    // function of the two remaining arguments `m` and `n`.
    let row_ty = d.arrow(nat, nat_to_nat);

    // --- Nat.landAux : Nat -> Nat -> Nat -> Nat -----------------------------
    {
        // fuel = zero: constant-zero row, regardless of m, n.
        let zero_minor = {
            let m_fv = d.fresh_fvar();
            let n_fv = d.fresh_fvar();
            let zero = d.zero();
            let with_n = d.lam_fv(n_fv, nat, zero);
            d.lam_fv(m_fv, nat, with_n)
        };

        // fuel = succ predecessor: guard on `n = 0` OUTERMOST, then `m = 0`
        // -- see the module doc for why the order is load-bearing. Both
        // branches select `0`; the third case is the real AND-at-this-bit
        // step, `2 * row(m/2, n/2) + (m%2)*(n%2)`, where `row` is the
        // recursive call at the smaller fuel.
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
            let bit_and = d.mul(bit_m, bit_n);
            let stepped = d.add(doubled, bit_and);

            let m_is_zero = d.beq(m, zero);
            let inner = d.bool_select_nat(m_is_zero, zero, stepped);
            let n_is_zero = d.beq(n, zero);
            let body = d.bool_select_nat(n_is_zero, zero, inner);

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
            name: p.land_aux,
            uparams: vec![],
            // Strictly greater than the height of everything it calls
            // (`Nat.div`/`Nat.mod` are height 3, `Nat.mul`/`Nat.beq` are
            // lower still) -- matches `log_aux`'s choice for the identical
            // call-graph shape.
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.land m n := Nat.landAux m m n ----------------------------------
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = land_aux(d, &p, m, m, n);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(m_fv, nat, with_n)
        };
        let ty = d.arrow(nat, nat_to_nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.land,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // land_zero_left : ∀ n, Eq (land 0 n) 0 -- refl: fuel = m = 0 exhausts
    // the outer Nat.rec immediately, regardless of n. See module doc.
    d.theorem(p.land_zero_left, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();
        let lhs = land(d, &p, zero, n);
        (d.eq(lhs, zero), d.refl(lhs))
    })?;

    // land_zero_right : ∀ m, Eq (land m 0) 0 -- induction on m to expose the
    // fuel's constructor; base and step are both `refl`, no induction
    // hypothesis used, because the `n = 0` guard (tested outermost)
    // collapses the whole succ-step term regardless of the predecessor --
    // exactly `log_zero_left`'s shape. See module doc.
    d.theorem(p.land_zero_right, 1, &|d, values| {
        let m = values[0];
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| {
            let zero = d.zero();
            let lhs = land(d, &p, candidate, zero);
            d.eq(lhs, zero)
        };
        let proof = d.induct(
            &statement_at,
            &|d| {
                let zero = d.zero();
                let lhs = land(d, &p, zero, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let candidate = d.succ(predecessor);
                let zero = d.zero();
                let lhs = land(d, &p, candidate, zero);
                d.refl(lhs)
            },
            m,
        );
        let stmt = statement_at(d, m);
        (stmt, proof)
    })?;

    // land_one_one : Eq (land 1 1) 1 -- one fuel step, both bits set:
    // 2 * landAux 0 0 0 + 1*1 = 0 + 1 = 1. Fully concrete, closes by refl.
    d.theorem(p.land_one_one, 0, &|d, _values| {
        let one = d.num(1);
        let lhs = land(d, &p, one, one);
        (d.eq(lhs, one), d.refl(lhs))
    })?;

    // land_three_five : Eq (land 3 5) 1 -- 011 & 101 = 001. Two fuel steps
    // with genuinely DIFFERING bit patterns at each position (unlike
    // `land_one_one`, whose single bit matches on both operands), so this is
    // the sanity check that would catch a wrong-way `bit_and` (e.g. `1 -
    // (m%2)*(n%2)`, an OR-shaped or negated step) that `land_one_one` alone
    // cannot distinguish from the correct AND.
    d.theorem(p.land_three_five, 0, &|d, _values| {
        let three = d.num(3);
        let five = d.num(5);
        let one = d.num(1);
        let lhs = land(d, &p, three, five);
        (d.eq(lhs, one), d.refl(lhs))
    })?;

    Ok(())
}
