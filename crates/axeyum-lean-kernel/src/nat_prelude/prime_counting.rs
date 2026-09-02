//! Four constructions that open two fresh nursery families, and NOTHING else.
//!
//! ADR-1556 refused nursery draw 19 on a measurement: over 40,668 distinct
//! drawn tens only three survive every held-out screen, all three draw rows
//! from the same four modules, and a module belongs to exactly one family, so
//! R5's two module-disjoint held-out families are unsatisfiable. Its named
//! unblock is ADR-1420 Route 1 — *declare a construction that opens a
//! topic-clean, vocabulary-clean module disjoint from those four*.
//!
//! This file is that route, for two modules
//! ([ADR-1559](../../../../../docs/research/09-decisions/adr-1559-primecounting-and-lcmupto-are-the-construction-that-unblocks-draw-19.md)):
//!
//! | construction | opens | pool | module-disjoint viable tens |
//! | --- | --- | ---: | ---: |
//! | [`Nat.primeCounting'`](NatPrelude::prime_counting_prime) / [`Nat.primeCounting`](NatPrelude::prime_counting) | `Mathlib.NumberTheory.PrimeCounting` | 9 rows | 0 → 5 |
//! | [`Nat.lcmUpto`](NatPrelude::lcm_upto) | `Mathlib.NumberTheory.Chebyshev` | 3 rows | 5 → 16 |
//!
//! **ADR-0653: the DEFINITIONS and their evaluation tests, and no theorems
//! about them.** Not even the defining equations, which the two sibling
//! construction files (`count_and_div_max_pow.rs`, `factorization_lcm.rs`)
//! also omit — and here there is a measured reason beyond precedent, below.
//!
//! ## `Nat.isPrime` — a divisor COUNT, not a trial division
//!
//! Mathlib's `Nat.primeCounting'` is `Nat.count Nat.Prime`, a count over a
//! classically-decidable predicate. This kernel declares no `Nat.Prime` and no
//! `DecidablePred`; it spells primality as an `And`, and
//! [`Nat.count`](NatPrelude::count) takes a `Nat → Bool`. So the pair needs a
//! `Bool` primality predicate, and the cheap one here is not trial division:
//!
//! ```text
//! isPrime n := beq (countRange (fun d => beq (n % (d+1)) 0) n) 2
//! ```
//!
//! [`countRange`](NatPrelude::count_range) folds over `d < n`, so
//! `d+1` ranges over `1 … n` and the fold counts the divisors of `n` in that
//! range. `n` is prime exactly when it has two. No fuel recursion, no `Bool`
//! conjunction, no new recursion principle — only `countRange`, `mod`, `succ`
//! and `beq`, every one of them already declared far above.
//!
//! Both degenerate rows fall out of the fold rather than being chosen
//! conventions: `n = 0` folds over nothing and counts `0`, and `n = 1` counts
//! only the divisor `1`; neither is `2`, so neither is prime.
//!
//! `Nat.isPrime` is NOT Mathlib's `Nat.Prime` — a `Bool` predicate with a
//! different construction — so by the mirror-flip criterion in `CLAUDE.md`
//! this is the `Nat.count`/`Nat.nth` case and not the
//! `Nat.descFactorial_of_lt` case: no `ml430` mirror stated against
//! `Nat.Prime` may be flipped on account of it. Measured against the pinned
//! statement inventory, no Mathlib row is NAMED `Nat.isPrime` and no row's
//! type mentions it, so it opens nothing by itself and collides with nothing
//! at R9.
//!
//! ## `Nat.primeCounting'` / `Nat.primeCounting`, and the row that is `rfl`
//!
//! `primeCounting' n` counts the primes strictly below `n`; `primeCounting n`
//! counts the primes up to and including `n`. Those are Mathlib's conventions
//! (`primeCounting' = Nat.count Nat.Prime`, `primeCounting n = primeCounting'
//! (n + 1)`), and this file takes them verbatim.
//!
//! Taking them verbatim has one measured consequence, published rather than
//! hidden: the candidate row
//! `Nat.primeCounting_eq_primeCounting'_succ : ∀ n, n.primeCounting = (n + 1).primeCounting'`
//! is **Mathlib's own defining equation** — the same inventory carries
//! `Nat.primeCounting.eq_1` stating it verbatim — so it is `rfl` here, with
//! `n` still a free variable, exactly as it is `rfl` in Mathlib. Declaring one
//! of the pair without the other opens no viable family at all (measured: 0
//! tens either way), so the pair is the unit and the row cannot be avoided by
//! declaring less.
//!
//! What it CAN be avoided by is declaring more, which is why `Nat.lcmUpto` is
//! here: `Nat.lcmUpto_*` sorts ahead of `Nat.monotone_*` and
//! `Nat.primeCounting_*`, so it displaces that row out of the
//! alphabetically-first ten a draw takes. Measured: 16 viable module-disjoint
//! tens, **8 of them carrying no definitional row**. The alternative — giving
//! `primeCounting` a deliberately non-definitional body so the row becomes a
//! genuine theorem — was rejected as tuning the blind population, which is the
//! thing the split policy exists to prevent.
//!
//! This is also why not even the defining equations are declared here. For
//! this construction the defining equation of the pair IS a candidate held-out
//! row, and a `refl` equation about `primeCounting` under any name would put a
//! second statement of it into the environment.
//!
//! ## `Nat.lcmUpto`
//!
//! `lcmUpto n` is `lcm(1, …, n)`, Mathlib's `(Finset.Icc 1 n).lcm id`, as a
//! structural fold with `lcmUpto 0 = 1` — the empty range's lcm, which is the
//! value Mathlib's own `Icc 1 0 = ∅` gives.
//!
//! ```text
//! lcmUpto n := Nat.rec 1 (fun j ih => lcm ih (j+1)) n
//! ```
//!
//! Every value below was produced by an independent Python reference
//! (`math.lcm` over `range(1, n+1)`; a sieve of Eratosthenes for the prime
//! counts) and checked against these definitions over `n < 40` before any of
//! this was written, and each evaluation-test control was checked to actually
//! separate the two sides — a control inherited from a sibling operator is
//! frequently vacuous.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// `Nat.isPrime`, `Nat.primeCounting'`, `Nat.primeCounting` and
/// `Nat.lcmUpto`. Definitions only.
pub(super) fn declare_prime_counting(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let bool_ty = d.bool_ty();

    // Nat.isPrime (n : Nat) : Bool :=
    //   beq (countRange (fun j => beq (mod n (succ j)) 0) n) 2
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let divides = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let candidate = d.succ(j);
            let remainder = d.modulo(n, candidate);
            let zero = d.zero();
            let body = d.beq(remainder, zero);
            d.lam_fv(j_fv, nat, body)
        };
        let divisors = d.const_app(p.count_range, &[divides, n]);
        let two = d.num(2);
        let body = d.beq(divisors, two);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, bool_ty);
        // Strictly greater delta height than `countRange` (12), `mod` (3) and
        // `beq` (1), the definitions it calls.
        d.kernel().add_declaration(Declaration::Definition {
            name: p.is_prime,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(13),
        })?;
    }

    // Nat.primeCounting' (n : Nat) : Nat := count isPrime n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let predicate = d.const_app(p.is_prime, &[]);
        let body = d.const_app(p.count, &[predicate, n]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, nat);
        // Strictly greater height than `count` (13) and `isPrime` (13).
        d.kernel().add_declaration(Declaration::Definition {
            name: p.prime_counting_prime,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(14),
        })?;
    }

    // Nat.primeCounting (n : Nat) : Nat := primeCounting' (succ n)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let successor = d.succ(n);
        let body = d.const_app(p.prime_counting_prime, &[successor]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, nat);
        // Strictly greater height than `primeCounting'` (14).
        d.kernel().add_declaration(Declaration::Definition {
            name: p.prime_counting,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(15),
        })?;
    }

    // Nat.lcmUpto (n : Nat) : Nat := Nat.rec 1 (fun j ih => lcm ih (succ j)) n
    {
        let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let base = d.num(1);
        let step = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let candidate = d.succ(j);
            let body = d.const_app(p.lcm, &[ih, candidate]);
            let with_ih = d.lam_fv(ih_fv, nat, body);
            d.lam_fv(j_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let one_lvl = d.level_one();
        let rec = d.kernel().const_(p.rec, vec![one_lvl]);
        let body = d.apply(rec, &[motive, base, step, n]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, nat);
        // Strictly greater height than `lcm` (11), the single definition it
        // calls.
        d.kernel().add_declaration(Declaration::Definition {
            name: p.lcm_upto,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(12),
        })?;
    }

    Ok(())
}
