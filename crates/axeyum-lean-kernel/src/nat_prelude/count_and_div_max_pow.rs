//! Two constructions that open two fresh nursery families, and NOTHING else.
//!
//! ADR-1420 measured that a refill draw is refused: R5 needs two NEW held-out
//! families, `_with_cycle` yields `ceil(n/3)` held-out so a draw needs `n >= 4`
//! fresh families, and at most one held-out-safe family was constructible from
//! the modules statable at the time. Its Route 1 is the remedy: *declare a
//! construction that opens a topic-clean, vocabulary-clean module*.
//!
//! This file is that route, for two modules:
//!
//! | construction | opens | pool | R11 vocabulary |
//! | --- | --- | ---: | --- |
//! | [`Nat.count`](NatPrelude::count) | `Mathlib.Data.Nat.Count` | 22 rows | 0 of 10 |
//! | [`Nat.divMaxPow`](NatPrelude::div_max_pow) | `Mathlib.Data.Nat.MaxPowDiv` | 7 rows | 0 of 7 |
//!
//! **ADR-0653: the DEFINITION and its evaluation test, and no theorems about
//! it.** A lane that declared seven supporting lemmas alongside `Nat.dist` on
//! 2026-08-30 spent the family it was opening — five carried exact Mathlib
//! mirror names and two sorted into the alphabetically-first ten a draw takes,
//! and R9 refused the family. The useful lemmas can land the day after the
//! draw, from `development`, where they cost nothing.
//!
//! ## `Nat.count` — an alias, and the disclosure that goes with it
//!
//! Mathlib's `Nat.count (p : ℕ → Prop) [DecidablePred p] (n : ℕ)` is
//! `(List.range n).countP p` — a `List` fold over a classically-decidable
//! predicate. This kernel has no `List` and no `DecidablePred`, and it already
//! has the same function under a different name and a `Bool`-valued predicate:
//! [`Nat.countRange`](NatPrelude::count_range) (`totient.rs`), `countRange p n
//! := Nat.rec 0 (fun j ih => ih + if p j then 1 else 0) n`.
//!
//! So `Nat.count` here is DEFINITIONALLY `Nat.countRange`, and that is stated
//! rather than hidden. Two consequences, both deliberate:
//!
//! * Per the mirror-flip criterion in `CLAUDE.md`, this is the
//!   `Nat.minFac`/`Nat.nth` case and not the `Nat.descFactorial_of_lt` case —
//!   our definitional body is a different construction from Mathlib's — so
//!   every `ml430` mirror stated against Mathlib's `Nat.count` stays `open`
//!   and must be proved, not flipped.
//! * The kernel already carries **19** `countRange` lemmas. Anyone
//!   preregistering `Mathlib.Data.Nat.Count` as a *held-out* family must
//!   record that in `holdout-adjacency-review-v1.json` before drawing —
//!   R11's environment sweep raises it (`('count', …, 40)`) and refuses the
//!   draw until a review exists, which is exactly the mechanism working.
//!
//! ## `Nat.divMaxPow` — genuinely new
//!
//! `Nat.divMaxPow n p` is `n` with every factor of `p` divided out: the
//! `p`-free part, `ordCompl[p] n`. Nothing in this kernel computes it —
//! `maxPow`, `divMaxPow`, `padic`, `ordCompl` and `multiplicity` all return
//! **zero** declarations from the environment snapshot.
//!
//! It is a fuel recursion in the same style as `Nat.nthAux`/`Nat.landAux`,
//! with the fuel and the shrinking value both taken from `n`:
//!
//! ```text
//! divMaxPowAux 0        n p := n
//! divMaxPowAux (succ f) n p :=
//!   if p <= 1        then n           -- p = 0 and p = 1 are Mathlib's conventions
//!   else if n = 0    then 0
//!   else if n % p = 0 then divMaxPowAux f (n / p) p
//!   else n
//! divMaxPow n p := divMaxPowAux n n p
//! ```
//!
//! **The fuel-exhaustion row returns `n`, not `0`**, and that is forced rather
//! than chosen: the recursion stops at the first `n` with `n % p /= 0` and
//! returns exactly that `n`, so the pass-through is `lor`'s shape and not
//! `land`'s (`CLAUDE.md`'s absorbing-zero table). Fuel `n` is more than
//! sufficient — every recursive step divides by a `p >= 2`, so at most
//! `log2 n + 1` steps occur — and the `p <= 1` guard is what keeps the
//! `p = 1` case from consuming fuel forever.
//!
//! Both boundary conventions are the ones Mathlib's own rows assert:
//! `divMaxPow 0 p = 0`, `divMaxPow 1 p = 1`, `divMaxPow n 1 = n`,
//! `divMaxPow n 0 = n`, `divMaxPow p p = 1` for `p /= 0`. The recursion was
//! simulated against an independent Python reference over `n < 60`, `p < 8`
//! (480 pairs, zero mismatches) before any of this was written, and each
//! evaluation-test control was checked to actually separate the two sides —
//! a control inherited from a sibling operator is frequently vacuous.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// `Nat.count`, `Nat.divMaxPowAux` and `Nat.divMaxPow`. Definitions only.
pub(super) fn declare_count_and_div_max_pow(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    // Nat.count (dec : Nat -> Bool) (n : Nat) : Nat := Nat.countRange dec n
    {
        let dec_fv = d.fresh_fvar();
        let dec = d.kernel().fvar(dec_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.count_range, &[dec, n]);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(dec_fv, pred_ty, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, nat);
            d.arrow(pred_ty, over_n)
        };
        // Strictly greater delta height than `countRange` (12), the single
        // definition it calls.
        d.kernel().add_declaration(Declaration::Definition {
            name: p.count,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(13),
        })?;
    }

    // Nat.divMaxPowAux (fuel n base : Nat) : Nat
    {
        // The motive over `fuel` is the constant family `Nat -> Nat -> Nat`
        // (from `n`, `base` to the result) -- `Nat.nthAux`'s device, with two
        // trailing accumulator arguments applied after the recursor.
        let nb_to_nat = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        let motive = d.kernel().lam(anon, nat, nb_to_nat, BinderInfo::Default);

        // base (fuel = 0): fun n base => n
        let base_case = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let b_fv = d.fresh_fvar();
            let inner = d.lam_fv(b_fv, nat, n);
            d.lam_fv(n_fv, nat, inner)
        };

        // step (predFuel, ih : Nat -> Nat -> Nat): fun n base => ...
        let step = {
            let predfuel_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let n_fv = d.fresh_fvar();
            let b_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let b = d.kernel().fvar(b_fv);

            let zero = d.zero();
            let one = d.num(1);
            let base_le_one = d.ble(b, one);
            let n_is_zero = d.beq(n, zero);
            let rem = d.modulo(n, b);
            let divides = d.beq(rem, zero);
            let quotient = d.div(n, b);
            let recurse = d.apply(ih, &[quotient, b]);
            // innermost: if n % base = 0 then recurse else n
            let divides_branch = d.bool_select_nat(divides, recurse, n);
            // if n = 0 then 0 else <above>
            let nonzero_branch = d.bool_select_nat(n_is_zero, zero, divides_branch);
            // if base <= 1 then n else <above>
            let body = d.bool_select_nat(base_le_one, n, nonzero_branch);

            let with_b = d.lam_fv(b_fv, nat, body);
            let with_n = d.lam_fv(n_fv, nat, with_b);
            let with_ih = d.lam_fv(ih_fv, nb_to_nat, with_n);
            d.lam_fv(predfuel_fv, nat, with_ih)
        };

        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let one_lvl = d.level_one();
        let rec = d.kernel().const_(p.rec, vec![one_lvl]);
        let nb_fn = d.apply(rec, &[motive, base_case, step, fuel]);

        let n2_fv = d.fresh_fvar();
        let b2_fv = d.fresh_fvar();
        let n2 = d.kernel().fvar(n2_fv);
        let b2 = d.kernel().fvar(b2_fv);
        let body = d.apply(nb_fn, &[n2, b2]);

        let value = {
            let with_b = d.lam_fv(b2_fv, nat, body);
            let with_n = d.lam_fv(n2_fv, nat, with_b);
            d.lam_fv(fuel_fv, nat, with_n)
        };
        let ty = {
            let over_nb = {
                let inner = d.arrow(nat, nat);
                d.arrow(nat, inner)
            };
            d.arrow(nat, over_nb)
        };
        // Strictly greater delta height than `div`/`mod`/`beq`/`ble`, the
        // definitions it calls (`bool_select_nat` is an inlined `Bool.rec`, not
        // a named constant, so it carries no height of its own).
        d.kernel().add_declaration(Declaration::Definition {
            name: p.div_max_pow_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // Nat.divMaxPow (n base : Nat) : Nat := divMaxPowAux n n base
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = d.const_app(p.div_max_pow_aux, &[n, n, b]);
        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(n_fv, nat, with_b)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        // Strictly greater height than `divMaxPowAux` (6).
        d.kernel().add_declaration(Declaration::Definition {
            name: p.div_max_pow,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })?;
    }

    Ok(())
}
