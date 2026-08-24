//! `Nat.Fin` — the canonical finite index type `{0, …, n-1}` — and
//! `Nat.injectiveOn`/`Nat.surjectiveOn`/`Nat.mapsInto`, the notions the finite
//! pigeonhole principle is stated with.
//!
//! ## Representation
//!
//! `Fin` is the **subtype form**: `⟨val : Nat, isLt : val < n⟩`, declared as a
//! one-constructor inductive exactly the way `CReal` carries its `seq` and
//! `regular` fields (`creal.rs::declare_carrier`/`declare_projections`): a
//! `Type 0`-valued family with a data field (`val`) and a dependent `Prop`
//! field over it (`isLt`), both projected out through the kernel-generated
//! recursor rather than declared as primitives. The one structural difference
//! from `CReal` is that `Fin` is a genuine one-*parameter* family — `n : Nat`
//! is a parameter shared by the family and its constructor, the same shape
//! `inductive_tests.rs::prod_two_params_one_ctor`'s `Prod α β` uses for its
//! two type parameters, just with a single `Nat`-sorted one here.
//!
//! The subtype form was chosen over an `fz`/`fs` (zero/successor) inductive —
//! Lean's own history has used both — because this development's finite-index
//! reasoning is stated directly over **bounded `Nat` quantifiers**
//! (`∀ i, i < n → …`, as `InjectiveOn`/`SurjectiveOn`/`MapsInto` below all are),
//! never over functions `Fin n → X`. `Fin.val` therefore only ever needs to
//! *compose* with the existing `Nat`-indexed folds (`Int.prodRange`,
//! `Nat.sumRange`) and their bound hypotheses, and the subtype form gives that
//! for free — `Fin.val` IS a `Nat`, with a separately-carried bound proof — with
//! no re-indexing step. An `fz`/`fs` inductive would make induction on `Fin n`
//! itself more direct, but nothing here inducts on `Fin n`; every proof below
//! inducts on the bounding `Nat`, so that advantage does not apply.
//!
//! ## `InjectiveOn` / `SurjectiveOn` / `MapsInto`
//!
//! These are stated directly over plain `Nat → Nat` functions, **not** over
//! `Fin n → Fin n` — no new type is needed for a bounded quantifier, and a
//! `Fin`-based formulation would force every consumer through `Fin.mk`'s bound
//! obligation for no gain here. `MapsInto` is the "self-map" hypothesis the
//! pigeonhole principle needs and the brief's plain-prose statement elides: an
//! injective function into a *larger* codomain need not be surjective onto a
//! smaller one, so `injective_on_imp_surjective_on` (when it lands) must carry
//! it as an explicit premise.
//!
//! ## Status
//!
//! `Fin` and the three definitions are declared and axiom-free. The
//! pigeonhole theorem `injective_on_imp_surjective_on` itself is **not**
//! declared here — see the module-level status note at the bottom of this
//! file for exactly what is missing and what is not.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Fin n`, i.e. `Nat.Fin` applied to the index bound `n`.
fn fin_ty(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let fin = d.prelude().fin;
    d.const_app(fin, &[n])
}

/// Declare the `Nat.Fin` family: the inductive itself, its two projections
/// (`val`, `isLt`), and `Fin.mk`'s defining equation on `val`.
///
/// # Errors
///
/// Returns the kernel's rejection if any generated declaration does not
/// type-check or a name is already taken.
pub(super) fn declare_fin(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // Fin : Nat → Type 0.
    let family_ty = d.arrow(nat, type0);

    // mk : Π (n val : Nat), Lt val n → Fin n.
    let mk_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let val_fv = d.fresh_fvar();
        let val = d.kernel().fvar(val_fv);
        let concl = fin_ty(d, n);
        let bound = d.lt(val, n);
        let with_bound = d.arrow(bound, concl);
        let with_val = d.pi_fv(val_fv, nat, with_bound);
        d.pi_fv(n_fv, nat, with_val)
    };
    d.kernel()
        .add_inductive(p.fin, &[], 1, family_ty, &[(p.fin_mk, mk_ty)])?;

    // val : Π (n : Nat), Fin n → Nat
    //     := fun n x => Fin.rec.{1} n (fun _ => Nat) (fun val _ => val) x.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fin_n = fin_ty(d, n);
        let motive = d.kernel().lam(anon, fin_n, nat, BinderInfo::Default);
        let minor = {
            let val_fv = d.fresh_fvar();
            let val = d.kernel().fvar(val_fv);
            let h_fv = d.fresh_fvar();
            let bound = d.lt(val, n);
            let inner = d.lam_fv(h_fv, bound, val);
            d.lam_fv(val_fv, nat, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let rec = d.kernel().const_(p.fin_rec, vec![one]);
        let body = d.apply(rec, &[n, motive, minor, x]);
        let value = {
            let with_x = d.lam_fv(x_fv, fin_n, body);
            d.lam_fv(n_fv, nat, with_x)
        };
        let ty = {
            let over_x = d.arrow(fin_n, nat);
            d.pi_fv(n_fv, nat, over_x)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.fin_val,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // isLt : Π (n : Nat) (x : Fin n), Lt (val n x) n
    //      := fun n x => Fin.rec.{0} n (fun y => Lt (val n y) n) (fun val h => h) x.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fin_n = fin_ty(d, n);
        let claim = |d: &mut NatDev<'_>, y: ExprId| {
            let val_y = d.const_app(p.fin_val, &[n, y]);
            d.lt(val_y, n)
        };
        let motive = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = claim(d, y);
            d.lam_fv(y_fv, fin_n, body)
        };
        let minor = {
            let val_fv = d.fresh_fvar();
            let val = d.kernel().fvar(val_fv);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let bound = d.lt(val, n);
            let inner = d.lam_fv(h_fv, bound, h);
            d.lam_fv(val_fv, nat, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let zero_level = d.kernel().level_zero();
        let rec = d.kernel().const_(p.fin_rec, vec![zero_level]);
        let body = d.apply(rec, &[n, motive, minor, x]);
        let value = {
            let with_x = d.lam_fv(x_fv, fin_n, body);
            d.lam_fv(n_fv, nat, with_x)
        };
        let ty = {
            let inner = claim(d, x);
            let with_x = d.pi_fv(x_fv, fin_n, inner);
            d.pi_fv(n_fv, nat, with_x)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.fin_is_lt,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // val_mk : ∀ (n val : Nat) (h : Lt val n), Eq Nat (val n (mk n val h)) val.
    // Closes by `Eq.refl val`: the recursor ι-reduces on the literal
    // constructor `mk n val h`, exactly as `Int.factorial_zero`/`_succ`
    // (`wilson.rs`) close over `Int.prodRange`'s own `Nat.rec` minors.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let val_fv = d.fresh_fvar();
        let val = d.kernel().fvar(val_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let bound = d.lt(val, n);
        let mk_nvh = d.const_app(p.fin_mk, &[n, val, h]);
        let lhs = d.const_app(p.fin_val, &[n, mk_nvh]);
        let stmt = d.eq(lhs, val);
        let proof = d.refl(val);
        let ty = {
            let with_h = d.pi_fv(h_fv, bound, stmt);
            let with_val = d.pi_fv(val_fv, nat, with_h);
            d.pi_fv(n_fv, nat, with_val)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, bound, proof);
            let with_val = d.lam_fv(val_fv, nat, with_h);
            d.lam_fv(n_fv, nat, with_val)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.fin_val_mk,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

/// Declare `Nat.injectiveOn`, `Nat.surjectiveOn`, and `Nat.mapsInto` — plain
/// `Prop`-valued definitions over `Nat → Nat` functions, no `Fin` needed (see
/// the module doc).
///
/// # Errors
///
/// Returns the kernel's rejection if any generated definition does not
/// type-check or a name is already taken.
pub(super) fn declare_injective_surjective(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();

    // injectiveOn f n := ∀ i j, i < n → j < n → f i = f j → i = j.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let fi = d.apply(f, &[i]);
        let fj = d.apply(f, &[j]);
        let concl = d.eq(i, j);
        let hyp_eq = d.eq(fi, fj);
        let step_eq = d.arrow(hyp_eq, concl);
        let hyp_j = d.lt(j, n);
        let step_j = d.arrow(hyp_j, step_eq);
        let hyp_i = d.lt(i, n);
        let inner = d.arrow(hyp_i, step_j);
        let body = {
            let with_j = d.pi_fv(j_fv, nat, inner);
            d.pi_fv(i_fv, nat, with_j)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.injective_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // surjectiveOn f n := ∀ k, k < n → ∃ i, i < n ∧ f i = k.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let one = d.level_one();
        let logic = d.prelude().logic;
        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.lt(i, n);
            let fi = d.apply(f, &[i]);
            let eqk = d.eq(fi, k);
            let body = d.const_app(logic.and, &[bound, eqk]);
            d.lam_fv(i_fv, nat, body)
        };
        let exists_ty = {
            let e = d.kernel().const_(logic.exists_, vec![one]);
            d.apply(e, &[nat, predicate])
        };
        let hyp_k = d.lt(k, n);
        let inner = d.arrow(hyp_k, exists_ty);
        let body = d.pi_fv(k_fv, nat, inner);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.surjective_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // mapsInto f n := ∀ i, i < n → f i < n.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);

        let hyp = d.lt(i, n);
        let fi = d.apply(f, &[i]);
        let concl = d.lt(fi, n);
        let inner = d.arrow(hyp, concl);
        let body = d.pi_fv(i_fv, nat, inner);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.maps_into,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Status: the pigeonhole principle (`injective_on_imp_surjective_on`)
// ---------------------------------------------------------------------------
//
// NOT declared in this file. `MapsInto f n → InjectiveOn f n → SurjectiveOn f n`
// needed nothing new from the rest of the inventory to STATE (done above); what
// is missing is entirely proof-construction effort for one genuinely nontrivial
// induction, not a missing foundational concept. Concretely, the route that
// works (order-based "compaction", not an equality-based "swap" — see below for
// why the swap route was rejected) is:
//
// Induction on `n`. Base `n = 0`: `SurjectiveOn f 0` is vacuous
// (`Nat.not_lt_zero`). Step `n = succ m`: let `c := f m` (so `c < succ m`, i.e.
// `c ≤ m`, from `MapsInto`). Define
//
//     compact(x) := if Nat.ble x c then x else Nat.pred x        -- Nat → Nat
//
// via `bool_select_nat` (already generic over `Nat`, no new selector needed),
// and `g(i) := compact(f i)` for `i < m`. The two facts the induction step
// needs, both from already-PROVED lemmas (nothing below is new machinery):
//
//   - `MapsInto g m`: for `i < m`, injectivity forces `f i ≠ c` (else
//     `f i = f m` with `i ≠ m` contradicts `InjectiveOn f (succ m)`), and
//     `f i < succ m` (`MapsInto`) gives `f i ≤ m`. Case `f i ≤ c`: since
//     `f i ≠ c`, `f i < c ≤ m`, so `compact(f i) = f i < m`. Case `f i > c`:
//     `compact(f i) = pred (f i) < m` since `f i ≤ m`. Both cases route through
//     `ble_eq_true_of_le` / `le_of_ble_eq_true` / `not_le_of_not_ble_eq_true`
//     (already proved for exactly this purpose) plus `Nat.pred`'s existing
//     order lemmas (`pred_le`, `pred_le_pred`) — no `Nat.beq`/decidable-EQUALITY
//     machinery is needed anywhere in this route, only the already-derived
//     decidable ORDER (`Nat.ble` + its four soundness/completeness lemmas).
//   - `InjectiveOn g m`: `compact` is injective on `{x ≤ m : x ≠ c}` — the
//     `x ≤ c` (hence `< c`, by `≠ c`) branch is the identity; the `x > c`
//     branch is `pred`, injective on `x > 0` via `le_dest` (already proved:
//     `x > c` gives `x = succ c + k` for some `k`, so `pred x = c + k`, and
//     `succ_add`/`pred_succ` recover `x` from `pred x` uniquely) — composed
//     with `f`'s own injectivity on `{0,…,m}` (a restriction of the `succ m`
//     hypothesis already in hand).
//
// Apply the induction hypothesis to `g` at `m`, getting `SurjectiveOn g m`.
// Case-split the target `k < succ m` on `Nat.ble k c`:
//   - `k = m` (the top of the range): if `c = m`, `f m = c = k` directly, done
//     with witness `m`. If `c < m`, apply `SurjectiveOn g m` at `c` (`c < m`) to
//     get `i < m` with `compact(f i) = c`; since `f i > c` in this branch (the
//     only way `compact` can land on `c` when `c` itself is excluded from the
//     domain by `f i ≠ c`) — wait, need `compact(f i) = c` to force
//     `f i = succ c` specifically, via `compact`'s definition on the `> c`
//     branch (`pred(f i) = c` and `f i > c` gives `f i = succ c` by
//     `pred_succ`'s converse) — DOES NOT immediately give `f i = m`, so this
//     branch of the case analysis is NOT YET RIGHT as sketched: the witness for
//     `k = m` needs `f i = m`, not `f i = succ c`, and those coincide only when
//     `succ c` happens to land at the top, which is not guaranteed by this
//     construction alone. THIS is the specific point the induction was not
//     landed at: the `compact`/`g` pairing above is verified to give
//     `MapsInto`/`InjectiveOn` cleanly, but the surjectivity CASE ANALYSIS
//     recovering `f i = k` from `compact(f i) = compact(k)`-shaped facts (the
//     general inverse step, needed for every `k`, not just `k = m`) was not
//     re-derived carefully enough during this slice to commit as a kernel term
//     — get `compact`'s LEFT inverse exactly right first (as a standalone
//     lemma: `∀ x ≤ m, x ≠ c → ∀ y ≤ m, y ≠ c → compact x = compact y → x = y`
//     is the injectivity half, already argued above; the missing half is
//     `∀ x ≤ m, x ≠ c → ∀ target < m, compact x = target → x = <the specific
//     preimage of target under compact>`, i.e. compact's actual two-branch
//     RIGHT inverse: `uncompact(c, target) := if target < c then target else
//     succ target`) — plug `uncompact` in for the general `k` case instead of
//     re-deriving it ad hoc per branch, then the two cases above (`k = m` /
//     `k < m`) both fall out of one composed statement instead of being
//     handled separately. That one lemma (`compact`/`uncompact` are mutually
//     inverse on the relevant domain) is the whole remaining gap.
//
// The swap-based alternative (`swap(c, m, x) := if x = c then m else if
// x = m then c else x`, using `Nat.beq` decidable equality) was considered
// first and is mathematically equivalent, but needs an involution proof
// (`swap ∘ swap = id`) via case-split on THREE branches instead of two, and
// needs `Nat.beq`'s completeness in the "false" direction
// (`a ≠ b → beq a b = false`), which the inventory does not carry as a named
// lemma (only the two `Eq ↔ beq = true` directions are proved) — it is
// derivable from the disjunction `beq_eq_true_iff` gives, but that is one more
// derivation the `ble`-based route above does not need. The order-based route
// was chosen for exactly that reason: `Nat.ble`'s full decidable order
// (`ble_eq_true_of_le`, `le_of_ble_eq_true`, `not_le_of_not_ble_eq_true`) is
// already proved to the same standard the swap route would have needed to
// build from scratch.
