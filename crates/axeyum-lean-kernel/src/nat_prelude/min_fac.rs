//! `Nat.minFac`: the least prime factor of `n`, by fuel-recursive linear
//! search over candidate divisors — see [`declare_min_fac_all`]'s doc comment
//! for the fuel-exhaustion choice, and the module-level note on why this is
//! NOT Mathlib's `def` even though the two compute identical values.
//!
//! ## Why this is not Mathlib's `minFac`, and why the mirror stays open
//!
//! Mathlib's `Nat.minFac n := if 2 ∣ n then 2 else minFacAux n 3`, where
//! `minFacAux` searches only ODD candidates starting at `3`, by
//! **well-founded recursion** on the strictly-decreasing measure
//! `sqrt n + 2 - k`, and terminates EARLY the moment `k * k > n` (returning
//! `n` itself, having proved `n` prime without checking any further
//! candidate). None of that is expressible as a *structural* `Nat.rec` — the
//! decrease is via `sqrt`, not a constructor predecessor — so building it
//! verbatim would need `WellFounded.fix`, which in this kernel is fine
//! (`lt_well_founded`, `ops.rs`) but is a materially different construction
//! from what is built here.
//!
//! What is built here instead is the simplest sound alternative: fuel
//! structural recursion (the same device `Nat.div`/`Nat.mod`/`Nat.log` use)
//! that tests EVERY candidate `2, 3, 4, …` in turn via `beq (mod n d) 0`,
//! exactly as `primes.rs`'s existing `least_divisor_search` decides
//! divisibility, with no even/odd skip and no early sqrt-bound exit. This
//! computes the identical VALUE as Mathlib's `minFac` for every `n` (both are
//! "the least divisor `≥ 2` of `n`, with `minFac 0 = 2` and `minFac 1 = 1` as
//! the same boundary conventions"), but by construction, not by algorithm:
//! the two are extensionally equal, not the same `def`.
//!
//! Per the established criterion (see `CLAUDE.md`'s "WHEN IS FLIPPING AN
//! `ml430` MIRROR HONEST" gotcha): flipping `F:ml430-nat-coprime-of-lt-minfac`
//! would require Mathlib's `minFac` and this one to be THE SAME definition,
//! not merely agree pointwise. They are not — this is the `Nat.multichoose`
//! case, not the `Nat.descFactorial_of_lt` case — so that mirror stays
//! `open`. A theorem about coprimality relative to THIS `minFac` would need
//! its own `F:nat-*` fact, not attempted in this lane (the minimality
//! property this `minFac` would need — `∀ d, 2 ≤ d → d ∣ n → minFac n ≤ d`
//! — is a further, separately-sized proof).
//!
//! ## The fuel-exhaustion base case
//!
//! `minFacAux` is called as `minFacAux (n - 2) n 2`: fuel `n - 2` and a
//! starting candidate `2` walk the candidate up to `n` in lockstep with the
//! fuel counting down to `0`, so fuel exhaustion (`fuel = 0`) coincides
//! EXACTLY with `candidate = n` — never earlier. So the base case "return the
//! candidate unchanged" is correct: it is only ever reached once every
//! candidate `2, …, n-1` has failed to divide `n`, and `n` trivially divides
//! itself, so returning `n` there is what continuing the search would have
//! found anyway (a prime `n`'s own least divisor `≥ 2` is itself).
//!
//! This is the boundary the module brief warns about: `minFac 0 = 2` and
//! `minFac 1 = 1` are handled by an outer case split BEFORE the fuel search
//! ever runs (`n - 2` truncates to `0` for `n < 2`, which would make the
//! search degenerate rather than wrong, but the two values are genuinely
//! different conventions, not a search result, so they get their own
//! branches).
//!
//! Any divisor found first, scanning upward from `2`, is automatically PRIME:
//! if the first divisor `d` found were composite, `d` would itself have a
//! divisor `2 ≤ e < d`, and `e ∣ d ∣ n` means `e` would have been found
//! first. So "first divisor found" and "smallest prime divisor" coincide for
//! this search, and `minFac 12 = 2` / `minFac 15 = 3` is exactly the
//! evaluation test (`min_fac.rs`'s own test module) discriminating a correct
//! search from one that returns the wrong candidate.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.minFacAux fuel n candidate`.
fn min_fac_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fuel: ExprId,
    n: ExprId,
    candidate: ExprId,
) -> ExprId {
    d.const_app(p.min_fac_aux, &[fuel, n, candidate])
}

/// `Nat.minFacAux` (structural fuel recursion, see the module doc) and
/// `Nat.minFac` (the two boundary cases plus the search).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_min_fac_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let level_one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);
    let nat_to_nat_to_nat = d.arrow(nat, nat_to_nat);

    // --- Nat.minFacAux : Nat -> Nat -> Nat -> Nat ---------------------------
    //
    // minFacAux zero n candidate        := candidate
    // minFacAux (succ f) n candidate    :=
    //   if beq (mod n candidate) 0 then candidate else minFacAux f n (succ candidate)
    {
        // fuel = zero: exhausted -- see the module doc for why returning the
        // candidate unchanged is correct here (it has already reached n).
        let zero_minor = {
            let n_fv = d.fresh_fvar();
            let candidate_fv = d.fresh_fvar();
            let candidate_var = d.kernel().fvar(candidate_fv);
            let with_candidate = d.lam_fv(candidate_fv, nat, candidate_var);
            d.lam_fv(n_fv, nat, with_candidate)
        };

        // fuel = succ f.
        let succ_minor = {
            let predecessor_fv = d.fresh_fvar();
            let row_fv = d.fresh_fvar();
            let row = d.kernel().fvar(row_fv);
            let n_fv = d.fresh_fvar();
            let n_var = d.kernel().fvar(n_fv);
            let candidate_fv = d.fresh_fvar();
            let candidate_var = d.kernel().fvar(candidate_fv);

            let remainder = d.modulo(n_var, candidate_var);
            let zero = d.zero();
            let is_divisor = d.beq(remainder, zero);
            let next_candidate = d.succ(candidate_var);
            let recurse = d.apply(row, &[n_var, next_candidate]);
            let body = d.bool_select_nat(is_divisor, candidate_var, recurse);

            let with_candidate = d.lam_fv(candidate_fv, nat, body);
            let with_n = d.lam_fv(n_fv, nat, with_candidate);
            let with_row = d.lam_fv(row_fv, nat_to_nat_to_nat, with_n);
            d.lam_fv(predecessor_fv, nat, with_row)
        };

        let motive = d
            .kernel()
            .lam(anon, nat, nat_to_nat_to_nat, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![level_one]);
        let fuel_fv = d.fresh_fvar();
        let fuel_var = d.kernel().fvar(fuel_fv);
        let row = d.apply(rec, &[motive, zero_minor, succ_minor, fuel_var]);
        let value_term = d.lam_fv(fuel_fv, nat, row);

        let ty = d.arrow(nat, nat_to_nat_to_nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.min_fac_aux,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.minFac n := if n=0 then 2 else if n=1 then 1 else
    //                     minFacAux (n-2) n 2 -------------------------------
    {
        let n_fv = d.fresh_fvar();
        let n_var = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);

        let is_zero = d.beq(n_var, zero);
        let is_one = d.beq(n_var, one);
        let fuel = d.sub(n_var, two);
        let searched = min_fac_aux(d, &p, fuel, n_var, two);
        let else_branch = d.bool_select_nat(is_one, one, searched);
        let body = d.bool_select_nat(is_zero, two, else_branch);

        let value_term = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.min_fac,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    Ok(())
}
