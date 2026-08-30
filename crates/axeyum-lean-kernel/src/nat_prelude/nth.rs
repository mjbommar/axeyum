//! `Nat.nth`: opens `Mathlib.Data.Nat.Nth` (pinned commit `c5ea0035…`, 11
//! rows) for the autogenesis screen — `docs/plan/status/348-nat-dist-nth.md`.
//!
//! ## Why this is NOT Mathlib's `nth`, and why the mirror stays open
//!
//! Mathlib's `Nat.nth (p : ℕ → Prop) (n : ℕ) : ℕ` is `noncomputable`: it case
//! splits on `Set.Finite (setOf p)` (decided by `Classical.propDecidable`,
//! not by any executable test) and, in the infinite branch, appeals to
//! `Nat.Subtype.orderIsoOfNat` — an order isomorphism built from the
//! set being infinite, again nonconstructively. Nothing about that is
//! structural or well-founded recursion over a decreasing `Nat` measure; it
//! is a classical case split over a `Prop`, and this kernel has neither
//! `Set`/`Finset` nor `Classical.choice` (see `CLAUDE.md`'s "`Prod` does not
//! exist" gotcha for the complete inductive list — `Set`/`Finset` are not on
//! it either). Reproducing it verbatim is not available here, at any cost.
//!
//! What is built here instead is the same honest substitution `Nat.minFac`
//! already uses (`min_fac.rs`'s module doc): a **computable, fuel-bounded**
//! search over a **`Bool`-valued** decision procedure, in the same fuel-
//! recursive style as `Nat.divMod`/`Nat.gcd`'s auxiliary state machines.
//! `Nat.nthAux dec fuel k n` walks candidates `k, k+1, k+2, …` for `fuel`
//! steps, testing `dec` at each; the `n`-th (0-indexed) candidate for which
//! `dec` is `true` is returned, and the sentinel `0` is returned if fewer
//! than `n+1` candidates satisfying `dec` are found within `fuel` steps —
//! matching Mathlib's own "0 if too few witnesses" convention
//! (`nth_of_card_le`), even though the MECHANISM (a hard search bound,
//! rather than classical case analysis on cardinality) is different.
//!
//! `Nat.nth dec bound n := nthAux dec bound 0 n`. The type
//! `(Nat → Bool) → Nat → Nat → Nat` is NOT Mathlib's `(ℕ → Prop) → ℕ → ℕ` —
//! an extra explicit `bound` replaces the classical finiteness case split,
//! and the predicate is decidable-by-construction rather than an arbitrary
//! `Prop`. Per the mirror-flip criterion (`CLAUDE.md`): this is the
//! `Nat.multichoose`/`Nat.minFac` case, not the `Nat.descFactorial_of_lt`
//! case — a different definition, extensionally agreeing wherever both are
//! defined — so any `ml430` mirror stated against Mathlib's `Nat.nth` stays
//! `open`. A theorem about THIS `nth` would need its own `F:nat-*` fact.
//!
//! No new well-founded-recursion machinery is needed: the fuel/`Bool.rec`
//! device is the same one `Nat.land`/`Nat.lor`/`Nat.beq`/`Nat.sumRange`
//! already use, generalized from one accumulator to two (`k`, the next
//! candidate to test, and `n`, the remaining count of matches needed).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// `Nat.nthAux` and `Nat.nth`.
pub(super) fn declare_nth_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let bool_ty = d.bool_ty();
    let dec_ty = d.arrow(nat, bool_ty); // Nat -> Bool

    // Nat.nthAux (dec : Nat -> Bool) (fuel k n : Nat) : Nat
    //   nthAux dec 0 k n ≡ 0
    //   nthAux dec (succ f) k n ≡
    //     if dec k then (if beq n 0 then k else nthAux dec f (succ k) (pred n))
    //              else nthAux dec f (succ k) n
    {
        // The motive over `fuel` is the constant family `Nat -> Nat -> Nat`
        // (from `k`, `n` to the result) — the same "outer motive, applied
        // afterward" device `Nat.beq`'s `Nat -> Bool` motive uses
        // (`defs.rs::declare_boolean_equality`), generalized to two trailing
        // accumulator arguments.
        let kn_to_nat = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        let motive = d.kernel().lam(anon, nat, kn_to_nat, BinderInfo::Default);

        let dec_fv = d.fresh_fvar();
        let dec = d.kernel().fvar(dec_fv);

        // base (fuel = 0): fun k n => 0
        let base = {
            let k_fv = d.fresh_fvar();
            let n_fv = d.fresh_fvar();
            let zero = d.zero();
            let inner = d.lam_fv(n_fv, nat, zero);
            d.lam_fv(k_fv, nat, inner)
        };

        // step (predFuel, ih : Nat -> Nat -> Nat): fun k n => …
        let step = {
            let predfuel_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let k_fv = d.fresh_fvar();
            let n_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let n = d.kernel().fvar(n_fv);

            let dec_k = d.apply(dec, &[k]);
            let sk = d.succ(k);
            let pn = d.pred(n);
            let zero = d.zero();
            let n_is_zero = d.beq(n, zero);
            let recurse_more_needed = d.apply(ih, &[sk, pn]);
            let found_branch = d.bool_select_nat(n_is_zero, k, recurse_more_needed);
            let not_found_branch = d.apply(ih, &[sk, n]);
            let body_kn = d.bool_select_nat(dec_k, found_branch, not_found_branch);

            let with_n = d.lam_fv(n_fv, nat, body_kn);
            let with_k = d.lam_fv(k_fv, nat, with_n);
            let with_ih = d.lam_fv(ih_fv, kn_to_nat, with_k);
            d.lam_fv(predfuel_fv, nat, with_ih)
        };

        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let one = d.level_one();
        let rec = d.kernel().const_(p.rec, vec![one]);
        let kn_fn = d.apply(rec, &[motive, base, step, fuel]); // : Nat -> Nat -> Nat

        let k2_fv = d.fresh_fvar();
        let n2_fv = d.fresh_fvar();
        let k2 = d.kernel().fvar(k2_fv);
        let n2 = d.kernel().fvar(n2_fv);
        let body = d.apply(kn_fn, &[k2, n2]);

        let value = {
            let with_n = d.lam_fv(n2_fv, nat, body);
            let with_k = d.lam_fv(k2_fv, nat, with_n);
            let with_fuel = d.lam_fv(fuel_fv, nat, with_k);
            d.lam_fv(dec_fv, dec_ty, with_fuel)
        };
        let ty = {
            let over_kn = {
                let inner = d.arrow(nat, nat);
                d.arrow(nat, inner)
            };
            let over_fuel_kn = d.arrow(nat, over_kn);
            d.arrow(dec_ty, over_fuel_kn)
        };
        // Strictly greater delta height than `beq`/`pred`/`succ`, the
        // definitions it calls (`bool_select_nat` is inlined `Bool.rec`, not
        // a named constant, so it carries no height of its own).
        d.kernel().add_declaration(Declaration::Definition {
            name: p.nth_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // Nat.nth (dec : Nat -> Bool) (bound n : Nat) : Nat := nthAux dec bound 0 n
    {
        let dec_fv = d.fresh_fvar();
        let dec = d.kernel().fvar(dec_fv);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let body = d.const_app(p.nth_aux, &[dec, bound, zero, n]);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            let with_bound = d.lam_fv(bound_fv, nat, with_n);
            d.lam_fv(dec_fv, dec_ty, with_bound)
        };
        let ty = {
            let over_bound_n = {
                let inner = d.arrow(nat, nat);
                d.arrow(nat, inner)
            };
            d.arrow(dec_ty, over_bound_n)
        };
        // Strictly greater height than `nthAux` (5).
        d.kernel().add_declaration(Declaration::Definition {
            name: p.nth,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    Ok(())
}
