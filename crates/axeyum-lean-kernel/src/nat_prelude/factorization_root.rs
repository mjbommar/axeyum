//! `Nat.ceilRoot` and `Nat.floorRoot` — the DIVISIBILITY roots, opening
//! `Mathlib.Data.Nat.Factorization.Root` for the autogenesis screen at cycle
//! index 3.
//!
//! ADR-1245 (this lane). ADR-1220 measured that draw 16 needs two viable
//! held-out slots, index 0 and index 3; ADR-1240 filled index 0 with
//! `Nat.casesOn` and the inductive `Nat.Primrec`. This is the other one.
//! Construction only (ADR-0653): no theorem about either is declared here, and
//! no fact is registered.
//!
//! ## These are not the numeric `n`-th root, and the distinction is the point
//!
//! `Nat.nthRoot k n` (draw 11, ADR-0910) is the greatest `m` with `m ^ k ≤ n`
//! — an ORDER statement, and the answer to "what is `⌊n^(1/k)⌋`".
//!
//! `Nat.floorRoot n a` is the greatest `b` with `b ^ n ∣ a`, and
//! `Nat.ceilRoot n a` the least `b ≥ 1` with `a ∣ b ^ n`. Both are
//! DIVISIBILITY statements, and they are the adjoints of `b ↦ b ^ n` on the
//! divisor lattice — which is why Mathlib defines them through
//! `Nat.factorization` and characterises them by
//! `a ^ n ∣ b ↔ a ∣ n.floorRoot b` and `a ∣ b ^ n ↔ n.ceilRoot a ∣ b`.
//!
//! They genuinely disagree with the numeric root, and the test file uses that
//! as its sharpest control: `floorRoot 2 12 = 2` while `⌊√12⌋ = 3`, and
//! `ceilRoot 2 12 = 6` while `⌈√12⌉ = 4`.
//!
//! ## The construction, and why it is not Mathlib's
//!
//! Mathlib (`Mathlib/Data/Nat/Factorization/Root.lean`):
//!
//! ```text
//! def Nat.floorRoot (n a : ℕ) : ℕ :=
//!   if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ (k / n)
//! def Nat.ceilRoot (n a : ℕ) : ℕ :=
//!   if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ ((k + n - 1) / n)
//! ```
//!
//! `Nat.factorization` is a `Finsupp` and this kernel has neither `Finsupp`
//! nor `Finset`, so that body cannot be written here at all. What CAN be
//! written is the extensional characterisation, as a bounded search:
//!
//! ```text
//! Nat.floorRoot n a := match n with
//!   | 0      => 0
//!   | succ m => Nat.rec 0 (fun b ih => if a % (b+1) ^ (m+1) == 0 then b+1 else ih) a
//! Nat.ceilRoot  n a := match n with
//!   | 0      => 0
//!   | succ m => (Nat.rec (fun _ => 0)
//!                        (fun _ g i => if i ^ (m+1) % a == 0 then i else g (i+1)) a) 1
//! ```
//!
//! `floorRoot` scans `b` DOWN from `a` and takes the first hit, so it returns
//! the greatest such `b`; `ceilRoot` scans `i` UP from `1` with `a` units of
//! fuel and takes the first hit, so it returns the least. Both bounds are
//! sound: `floorRoot n a ≤ a` because `b ^ n ∣ a` forces `b ≤ a` for `a ≠ 0`,
//! and `ceilRoot n a ≤ a` because `⌈k/n⌉ ≤ k` for `n ≥ 1`.
//!
//! **Verified against Mathlib's definition by simulation before any Rust was
//! written**, over every `(n, a)` with `n ∈ [0, 4]` and `a ∈ [0, 79]` — 400
//! pairs, computed both ways (prime factorisation with `⌊k/n⌋` / `⌈k/n⌉`, and
//! the bounded search), zero mismatches. That check is what a `Definition` gets
//! instead of a proof, and it is the reason it was run first: the kernel
//! type-checks `Nat → Nat → Nat` whatever the body computes.
//!
//! Per `CLAUDE.md`'s mirror-flip criterion this is the `Nat.multichoose` case,
//! not the `Nat.descFactorial_of_lt` case: Mathlib's is a product over a
//! `Finsupp` and ours is a search, so they are structurally different
//! constructions that agree extensionally. Every `ml430` mirror stated over
//! Mathlib's `Nat.ceilRoot`/`Nat.floorRoot` stays `open`, and a theorem about
//! OURS would need its own `F:nat-*` fact.
//!
//! ## The `a = 0` disjunct is deliberately dropped, and that is testable
//!
//! Mathlib guards on `n = 0 ∨ a = 0`. Only the `n = 0` half survives here,
//! because the other half is dead code in this construction: `floorRoot`'s
//! downward scan over `a = 0` hits its `Nat.rec` base case and returns `0`,
//! and `ceilRoot`'s upward scan has `0` fuel and returns `0`. A guard no input
//! can reach is a branch nothing can test, and this repository's standing rule
//! is that every branch of a definition needs a discriminating evaluation.
//! Both `_zero_right` statements still hold; they are no longer `Eq.refl`.
//!
//! ## What IS settled by reduction, disclosed rather than left to be found
//!
//! The drawn ten (ADR-1245's screen, run against the real `select()`) are
//! `ceilRoot_eq_zero`, `_ne_zero`, `_one_left`, `_one_right`, `_pow_self`,
//! `_zero_left`, `_zero_right`, `dvd_ceilRoot_pow`, `dvd_pow_iff_ceilRoot_dvd`
//! and `floorRoot_eq_zero`. Against THIS construction exactly ONE of them is
//! settled by reduction:
//!
//! * `Nat.ceilRoot_zero_left : ∀ a, Nat.ceilRoot 0 a = 0` — the guard is a
//!   `Nat.rec` on `n`, so at `n = 0` it ι-reduces to `0` at a free `a`. A
//!   boundary row, and it is disclosed as one.
//!
//! Two more deserve naming because they LOOK like boundary rows and are not:
//!
//! * `Nat.ceilRoot_zero_right : ∀ n, n.ceilRoot 0 = 0` is NOT `refl` here —
//!   the guard is stuck at a symbolic `n`. It is a two-case split whose
//!   branches are each `refl`, so it is cheap; it is not free.
//! * `Nat.ceilRoot_one_left : ∀ a, Nat.ceilRoot 1 a = a` is NOT `refl` here,
//!   which is the whole reason ADR-1220's inherited count of 3 had to be
//!   re-measured. At `n = 1` the guard reduces but the search's `Nat.rec` on
//!   the fuel `a` does not, so the statement carries the real content "the
//!   least `b ≥ 1` with `a ∣ b` is `a`".
//!
//! A definition that special-cased `n = 1` would settle it by reduction, and
//! that is precisely what ADR-1160 read Mathlib's shape as implying. No such
//! case was written, and none was removed to move a row either — the shape
//! above is the direct one.
//!
//! ## No theorems
//!
//! ADR-0653: an unblocking lane declares the construction and its evaluation
//! test and NOTHING else. The lane that also declared seven ordinary
//! supporting theorems had its family refused by R9 as no longer blind.
//! `floorRoot_pow_dvd`, `pow_dvd_iff_dvd_floorRoot` and the rest can land
//! tomorrow from `development`, where they cost nothing.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// Delta height for both definitions. Strictly above `Nat.pow` (3),
/// `Nat.mod` (3) and `Nat.beq`, the only `Nat` definitions either one calls.
const ROOT_HEIGHT: u16 = 6;

/// Declare `Nat.floorRoot` and `Nat.ceilRoot`. Definitions only — see this
/// module's doc for why no theorem about either is declared here.
///
/// Depends on `Nat.pow`, `Nat.mod`, `Nat.beq` and `Bool.rec`, all far above;
/// nothing later in `nat_prelude` needs it.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_factorization_root_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    declare_floor_root(d, &p)?;
    declare_ceil_root(d, &p)?;
    Ok(())
}

/// `Nat.floorRoot n a` — the greatest `b` with `b ^ n ∣ a`, and `0` when
/// `n = 0`.
fn declare_floor_root(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();

    let n_fv = d.fresh_fvar();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    // motive := fun (_ : Nat) => Nat, for both recursions.
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);

    // The outer guard is a `Nat.rec` on `n` rather than a `Bool` test, so the
    // `n = 0` branch ι-reduces at a free `a` exactly the way Mathlib's
    // `if n = 0 ∨ a = 0` does — and so that the `succ` branch has the
    // predecessor in hand without a second scrutinee.
    let guarded = {
        let m_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let exponent = d.succ(m);

        // step := fun b ih => if a % (succ b) ^ (succ m) == 0 then succ b else ih
        let step = {
            let b_fv = d.fresh_fvar();
            let inner_ih_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let inner_ih = d.kernel().fvar(inner_ih_fv);

            let candidate = d.succ(b);
            let power = d.pow(candidate, exponent);
            let remainder = d.modulo(a, power);
            let zero = d.zero();
            let divides = d.beq(remainder, zero);
            let body = d.bool_select_nat(divides, candidate, inner_ih);

            let with_ih = d.lam_fv(inner_ih_fv, nat, body);
            d.lam_fv(b_fv, nat, with_ih)
        };

        // Scan DOWN from `a`: `Nat.rec` reaches `succ b` before `b`, and the
        // first branch taken wins, so the first hit is the GREATEST such `b`.
        // The base case `0` is also the honest answer when nothing divides.
        let base = d.zero();
        let rec = d.kernel().const_(p.rec, vec![one]);
        let search = d.apply(rec, &[motive, base, step, a]);

        let with_ih = d.lam_fv(ih_fv, nat, search);
        d.lam_fv(m_fv, nat, with_ih)
    };

    let n = d.kernel().fvar(n_fv);
    let zero = d.zero();
    let rec = d.kernel().const_(p.rec, vec![one]);
    let applied = d.apply(rec, &[motive, zero, guarded, n]);

    let value = {
        let with_a = d.lam_fv(a_fv, nat, applied);
        d.lam_fv(n_fv, nat, with_a)
    };
    let ty = {
        let over_a = d.arrow(nat, nat);
        d.arrow(nat, over_a)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.floor_root,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ROOT_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.ceilRoot n a` — the least `b ≥ 1` with `a ∣ b ^ n`, and `0` when
/// `n = 0` or when the scan runs out of fuel (which happens exactly at
/// `a = 0`).
fn declare_ceil_root(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();

    let n_fv = d.fresh_fvar();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let motive_nat = d.kernel().lam(anon, nat, nat, BinderInfo::Default);

    let guarded = {
        let m_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let exponent = d.succ(m);

        // The upward scan carries its index, so the motive is the CONSTANT
        // family `fun _ => Nat → Nat` and the recursion is over the fuel.
        // This is the standard curried-accumulator shape (`Nat.fibAux`,
        // `Nat.xgcdAux`); a plain `Nat.rec` on the index cannot count up.
        let nat_to_nat = d.arrow(nat, nat);
        let motive = d.kernel().lam(anon, nat, nat_to_nat, BinderInfo::Default);

        // base := fun _ => 0 -- fuel exhausted, nothing found.
        let base = {
            let zero = d.zero();
            d.kernel().lam(anon, nat, zero, BinderInfo::Default)
        };

        // step := fun _ g => fun i => if i ^ (succ m) % a == 0 then i else g (succ i)
        let step = {
            let fuel_fv = d.fresh_fvar();
            let g_fv = d.fresh_fvar();
            let i_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let i = d.kernel().fvar(i_fv);

            let power = d.pow(i, exponent);
            let remainder = d.modulo(power, a);
            let zero = d.zero();
            let divided = d.beq(remainder, zero);
            let next = d.succ(i);
            let recurse = d.apply(g, &[next]);
            let body = d.bool_select_nat(divided, i, recurse);

            let with_i = d.lam_fv(i_fv, nat, body);
            let with_g = d.lam_fv(g_fv, nat_to_nat, with_i);
            d.lam_fv(fuel_fv, nat, with_g)
        };

        let rec = d.kernel().const_(p.rec, vec![one]);
        let scan = d.apply(rec, &[motive, base, step, a]);
        // Start at `i = 1`: `b = 0` is never a lawful answer, since `a ∣ 0 ^ n`
        // holds for every `a` and would make the least witness vacuously `0`.
        let start = d.num(1);
        let search = d.kernel().app(scan, start);

        let with_ih = d.lam_fv(ih_fv, nat, search);
        d.lam_fv(m_fv, nat, with_ih)
    };

    let n = d.kernel().fvar(n_fv);
    let zero = d.zero();
    let rec = d.kernel().const_(p.rec, vec![one]);
    let applied = d.apply(rec, &[motive_nat, zero, guarded, n]);

    let value = {
        let with_a = d.lam_fv(a_fv, nat, applied);
        d.lam_fv(n_fv, nat, with_a)
    };
    let ty = {
        let over_a = d.arrow(nat, nat);
        d.arrow(nat, over_a)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.ceil_root,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ROOT_HEIGHT),
    })?;
    Ok(())
}
