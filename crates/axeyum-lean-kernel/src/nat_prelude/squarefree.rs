//! `Squarefree` — opens `Mathlib.Data.Nat.Squarefree` (pinned commit
//! `c5ea0035…`, 11 rows) for the autogenesis screen, paired with
//! [`nth_root.rs`](super::nth_root)'s `Nat.nthRoot` (see that module's doc
//! for why the un-owned floor needs both together, not either alone).
//!
//! ## Bare root name, not `Nat.squarefree`
//!
//! Mathlib's `Squarefree (r : R) [Monoid R] : Prop := ∀ x, x * x ∣ r →
//! IsUnit x` lives at the **bare root namespace**, applied to `Nat` at the
//! use site (`Squarefree n` for `n : Nat`), not under a `Nat.` prefix — the
//! pinned inventory's raw `Lean.Expr` dump for e.g. `Nat.Squarefree.ext_iff`
//! applies the constant `` `Squarefree `` directly (with `Nat` and
//! `Nat.instMonoid` as explicit arguments), never `` `Nat.Squarefree ``.
//! The autogenesis screen extracts constants as literal tokens from that
//! dump, so opening the module requires a kernel declaration whose rendered
//! name is exactly `Squarefree`, not `Nat.Squarefree` — confirmed by
//! re-running the generator's own `admissible()` in memory before writing
//! anything here (this crate's CLAUDE.md brief / `docs/plan/status/`).
//!
//! ## `Bool`, not `Prop`, and no bridge
//!
//! A `Prop`-valued predicate cannot be evaluated at concrete arguments —
//! there is no normal form to compare against an independently computed
//! value, so no evaluation test could exist for it (this crate's CLAUDE.md
//! brief: "a `Bool`-valued decision procedure is evaluable at concrete
//! arguments — which is what makes an evaluation test possible at all").
//! So this file declares only the **executable** decision procedure
//! `Squarefree (n : Nat) : Bool`. A `Prop` restatement plus a
//! `Bool`-agrees-with-`Prop` bridge theorem is deliberately NOT built:
//! ADR-0653 asks for the construction and its evaluation test only, and a
//! bridge is a theorem *about* the construction, not part of it. (There is
//! also no `funext` in this kernel, so a bridge would need to be stated
//! pointwise via `Bool.rec`-style case analysis rather than function
//! extensionality — extra machinery this file has no use for.)
//!
//! This mirrors [`nth.rs`](super::nth)'s precedent exactly: that file
//! reuses Mathlib's `nth` name for a `(Nat -> Bool) -> Nat -> Nat -> Nat`
//! construction with a genuinely different type than Mathlib's `(ℕ -> Prop)
//! -> ℕ -> ℕ`, and any mirror theorem stated against the REAL, `Prop`-valued
//! `Squarefree` stays `open` here for exactly the same reason — this
//! declaration only OPENS the vocabulary; it proves nothing about Mathlib's
//! predicate.
//!
//! ## Recursion scheme
//!
//! `Nat.squarefreeAux (n fuel : Nat) : Nat -> Bool` is a fuel-bounded linear
//! search over candidate divisors `k`, structural recursion on `fuel` with
//! `n` captured free (never threaded through the motive) and `k` threaded
//! by the same "motive returns a function, applied afterward" device
//! [`nth.rs`](super::nth) uses for its own accumulator:
//!
//! ```text
//! squarefreeAux n 0        ≡ fun k => true
//! squarefreeAux n (succ f) ≡ fun k =>
//!   if beq (mod n (mul k k)) 0 then false else (squarefreeAux n f) (succ k)
//! ```
//!
//! `Squarefree n := if n == 0 then false else squarefreeAux n n 2` — search
//! starts at `k = 2` (the smallest candidate that is not a unit) and `n`
//! fuel steps always suffice: any `k >= 2` with `k * k ∣ n` and `n >= 1`
//! satisfies `k <= k * k <= n`, so every witness lies within `[2, n]`, well
//! inside the `n`-step search from `2`. The `n = 0` branch is mandatory:
//! Mathlib's own `Squarefree 0` is `False` (`x = 2` satisfies `x * x ∣ 0`,
//! since everything divides `0`, and `2` is not a unit in `ℕ`), and the
//! unguarded search would instead find every candidate's square dividing
//! `0` and immediately return `false` at `k = 2` — same answer here by
//! coincidence, but for the wrong reason and not for `n` in general, so the
//! branch is kept explicit rather than relied upon.
//!
//! No equation lemma or other theorem is declared here (ADR-0653): see
//! `nat_prelude_tests.rs`'s `squarefree_evaluates_correctly` for the
//! concrete instances checked (including the smallest non-squarefree
//! witness `4 = 2 * 2` and the boundary `n = 0`, `n = 1`).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `if condition then on_true else on_false` at `Bool` (i.e. `Bool.rec`
/// applied at a `Bool`-valued motive) — the `Bool`-codomain sibling of
/// [`NatOps::bool_select_nat`](super::ops::NatOps::bool_select_nat), needed
/// here because `Squarefree` itself is `Bool`-valued.
fn bool_select_bool(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `Nat.squarefreeAux n fuel k`.
fn squarefree_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    fuel: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.squarefree_aux, &[n, fuel, k])
}

/// Declare `Nat.squarefreeAux` and the bare-root `Squarefree`. Definitions
/// only — see this module's doc for why no theorem about either is
/// declared here.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_squarefree_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let bool_ty = d.bool_ty();
    let level_one = d.level_one();

    // --- Nat.squarefreeAux : Nat -> Nat -> (Nat -> Bool) --------------------
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);

        let nat_to_bool = d.arrow(nat, bool_ty);
        let motive = d.kernel().lam(anon, nat, nat_to_bool, BinderInfo::Default);

        // base (fuel = 0): fun k => true -- no candidate has been tested,
        // so nothing has been found to contaminate the search.
        let base = {
            let k_fv = d.fresh_fvar();
            let true_ = d.bool_true();
            d.lam_fv(k_fv, nat, true_)
        };

        // step (predFuel, ih : Nat -> Bool): fun k =>
        //   if beq (mod n (mul k k)) 0 then false else ih (succ k)
        let step = {
            let predfuel_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);

            let sq = d.mul(k, k);
            let rem = d.modulo(n, sq);
            let zero = d.zero();
            let divides = d.beq(rem, zero);
            let sk = d.succ(k);
            let keep_searching = d.apply(ih, &[sk]);
            let false_ = d.bool_false();
            let body_k = bool_select_bool(d, &p, divides, false_, keep_searching);

            let with_k = d.lam_fv(k_fv, nat, body_k);
            let with_ih = d.lam_fv(ih_fv, nat_to_bool, with_k);
            d.lam_fv(predfuel_fv, nat, with_ih)
        };

        let rec = d.kernel().const_(p.rec, vec![level_one]);
        let nk_fn = d.apply(rec, &[motive, base, step, fuel]); // : Nat -> Bool

        let k2_fv = d.fresh_fvar();
        let k2 = d.kernel().fvar(k2_fv);
        let body = d.apply(nk_fn, &[k2]);

        let value = {
            let with_k = d.lam_fv(k2_fv, nat, body);
            let with_fuel = d.lam_fv(fuel_fv, nat, with_k);
            d.lam_fv(n_fv, nat, with_fuel)
        };
        let ty = {
            let over_k = d.arrow(nat, bool_ty);
            let over_fuel_k = d.arrow(nat, over_k);
            d.arrow(nat, over_fuel_k)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.squarefree_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // --- Squarefree n := if n == 0 then false else squarefreeAux n n 2 -----
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let zero = d.zero();
        let two = d.num(2);
        let n_is_zero = d.beq(n, zero);
        let searched = squarefree_aux(d, &p, n, n, two);
        let false_ = d.bool_false();
        let body = bool_select_bool(d, &p, n_is_zero, false_, searched);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, bool_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.squarefree,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    Ok(())
}
