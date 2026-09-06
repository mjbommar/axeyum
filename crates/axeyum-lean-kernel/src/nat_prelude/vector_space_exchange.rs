//! `AlgS.Index.*` — ADR-1657, roadmap W3-2: the **index calculus** the
//! Steinitz exchange needs, built where it has to live.
//!
//! # The obstruction this file removes
//!
//! ADR-1627 stopped invariance of basis number at length zero
//! ([`super::vector_space::VectorSpaceNames::basis_zero_unique`]) and sized
//! the general theorem. Its obstruction was **not** the field and **not**
//! `Quot`: the exchange argument rewrites the *indexing* of a coefficient
//! family — drop index `i`, insert a vector at index `i` — and at the `AlgS`
//! build position the only `Nat` vocabulary that exists is `Nat`,
//! `Nat.zero`, `Nat.succ` and `Nat.rec`. `Nat.le`, `Nat.lt`, `Nat.beq` and
//! `Nat.ble` are interned some 60 lines *later* in `nat_prelude.rs`
//! (`Nat.le` at the `kernel.name_str(nat, "le")` call), and
//! `super::module_setoid`'s `coeffAgree` exists in the shape it does for
//! exactly this reason.
//!
//! # Route (b), and why not route (a)
//!
//! Two routes were on the table (ADR-1657 records the measurement):
//!
//! - **(a) thread `Nat.lt`/`Nat.beq`/`Nat.ble` in as explicit `deps`**, the
//!   way `structures_setoid` receives its `LogicPrelude` names. This does not
//!   work as stated. A `dep` is a `NameId` of a declaration that is *already
//!   in the environment*, and these four are not: they are declared after the
//!   whole `AlgS` block. Making them available means MOVING either the `Nat`
//!   arithmetic block up or the `AlgS` block down — a reordering of the
//!   shared prelude build, which is the single change the 2026-08-27
//!   architecture review names as the recurring source of phase-order bugs,
//!   and which every other lane's build shares.
//! - **(b) state the surgery over `Nat.rec`**, which is what this file does.
//!   It is additive, it needs no dep at all, and the resulting definitions
//!   have the *defining equations as ι-reductions* — every equation in the
//!   table below is `Eq.refl`, which is what makes the lemmas above them
//!   cheap.
//!
//! # What is declared
//!
//! | name | kind | what it is |
//! |---|---|---|
//! | `AlgS.Index.le` | definition | `m ≤ n`, by `Nat.rec` on `m` then on `n` |
//! | `AlgS.Index.removeAt` | definition | drop index `i` from a family, shift the rest down |
//! | `AlgS.Index.insertAt` | definition | insert a value at index `i`, shift the rest up |
//!
//! The seven defining equations, all definitional:
//!
//! ```text
//! le zero n                     ≡ True
//! le (succ i) zero              ≡ False
//! le (succ i) (succ n)          ≡ le i n
//! removeAt α zero v j           ≡ v (succ j)
//! removeAt α (succ i) v zero    ≡ v zero
//! removeAt α (succ i) v (succ j)≡ removeAt α i (fun t => v (succ t)) j
//! insertAt α zero w v zero      ≡ w
//! insertAt α zero w v (succ j)  ≡ v j
//! insertAt α (succ i) w v zero  ≡ v zero
//! insertAt α (succ i) w v (succ j) ≡ insertAt α i w (fun t => v (succ t)) j
//! ```
//!
//! `removeAt` and `insertAt` are stated over an explicit `α : Type` rather
//! than universe-polymorphically: every family this library forms is
//! `Nat -> <record>.carrier`, and a record carrier is `Sort 1` by
//! construction (`super::structures`'s `carrier_field`), so a `Sort u`
//! version would buy nothing and would need `imax` levels on four `Nat.rec`
//! motives.

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

use super::structures::{arrow, lam_over, pi_over};

// ---------------------------------------------------------------------------
// Free-variable block: 26_xxx, disjoint from `module_setoid` (23_xxx),
// `field_setoid` (24_xxx) and `vector_space` (25_xxx).
// ---------------------------------------------------------------------------

const AL_FV: u64 = 26_000;
const I_FV: u64 = 26_001;
const J_FV: u64 = 26_002;
const N_FV: u64 = 26_003;
const V_FV: u64 = 26_004;
const W_FV: u64 = 26_005;
const IH_FV: u64 = 26_006;
const T_FV: u64 = 26_007;
const SCRATCH_FV: u64 = 26_050;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

// ---------------------------------------------------------------------------
// `AlgS.Index.le`.
// ---------------------------------------------------------------------------

/// `AlgS.Index.le : Nat -> Nat -> Prop`, the order relation this shelf needs
/// because `Nat.le` is not declared yet.
///
/// Recursion on the FIRST argument returning a `Nat -> Prop`, then on the
/// second. The universe of both `Nat.rec`s is ONE, not zero, for the reason
/// `super::module_setoid`'s `coeffAgree` records: the recursion returns a
/// `Prop`-VALUED object, whose own sort is `Sort 1`.
fn declare_le(k: &mut Kernel, lg: &LogicPrelude, ns: NameId) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let nat = k.const_(lg.nat, vec![]);
    let prop = k.sort(l0);
    let nat_to_prop = arrow(k, nat, prop);

    let motive = lam_over(k, SCRATCH_FV, nat, nat_to_prop);
    let minor_zero = {
        let t = k.const_(lg.true_, vec![]);
        lam_over(k, SCRATCH_FV, nat, t)
    };
    let minor_succ = {
        let ih = k.fvar(IH_FV);
        let n = k.fvar(N_FV);
        let inner_motive = lam_over(k, SCRATCH_FV, nat, prop);
        let inner_zero = k.const_(lg.false_, vec![]);
        let inner_succ = {
            let j = k.fvar(J_FV);
            let body = k.app(ih, j);
            let body = lam_over(k, SCRATCH_FV, prop, body);
            lam_over(k, J_FV, nat, body)
        };
        let rec = k.const_(lg.nat_rec, vec![l1]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, n]);
        let body = lam_over(k, N_FV, nat, body);
        let body = lam_over(k, IH_FV, nat_to_prop, body);
        lam_over(k, I_FV, nat, body)
    };
    let i = k.fvar(I_FV);
    let n = k.fvar(N_FV);
    let rec = k.const_(lg.nat_rec, vec![l1]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let body = k.app(outer, n);
    let value = lam_over(k, N_FV, nat, body);
    let value = lam_over(k, I_FV, nat, value);

    let ty = {
        let inner = arrow(k, nat, prop);
        arrow(k, nat, inner)
    };

    let name = k.name_str(ns, "le");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// `AlgS.Index.removeAt` / `AlgS.Index.insertAt`.
// ---------------------------------------------------------------------------

/// `AlgS.Index.removeAt : forall (a : Type), Nat -> (Nat -> a) -> Nat -> a`.
///
/// `removeAt a i v` is `v` with index `i` deleted and everything above it
/// shifted down by one. Recursion on `i`, returning a family TRANSFORMER
/// (`(Nat -> a) -> (Nat -> a)`), so the recursive call can be made at the
/// shifted family `fun t => v (succ t)` — that is the whole reason the
/// motive is not simply `fun _ => Nat -> a`.
fn declare_remove_at(k: &mut Kernel, lg: &LogicPrelude, ns: NameId) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let ty1 = k.sort(l1);
    let nat = k.const_(lg.nat, vec![]);
    let nat_zero = k.const_(lg.nat_zero, vec![]);
    let nat_succ = k.const_(lg.nat_succ, vec![]);

    let al = k.fvar(AL_FV);
    let fam_ty = arrow(k, nat, al);
    let xform_ty = arrow(k, fam_ty, fam_ty);

    let motive = lam_over(k, SCRATCH_FV, nat, xform_ty);
    let minor_zero = {
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let sj = k.app(nat_succ, j);
        let body = k.app(v, sj);
        let body = lam_over(k, J_FV, nat, body);
        lam_over(k, V_FV, fam_ty, body)
    };
    let minor_succ = {
        let ih = k.fvar(IH_FV);
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let inner_motive = lam_over(k, SCRATCH_FV, nat, al);
        let inner_zero = k.app(v, nat_zero);
        let inner_succ = {
            let jp = k.fvar(T_FV);
            let shifted = {
                let t = k.fvar(N_FV);
                let st = k.app(nat_succ, t);
                let b = k.app(v, st);
                lam_over(k, N_FV, nat, b)
            };
            let applied = k.app(ih, shifted);
            let body = k.app(applied, jp);
            let body = lam_over(k, SCRATCH_FV, al, body);
            lam_over(k, T_FV, nat, body)
        };
        let rec = k.const_(lg.nat_rec, vec![l1]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, j]);
        let body = lam_over(k, J_FV, nat, body);
        let body = lam_over(k, V_FV, fam_ty, body);
        let body = lam_over(k, IH_FV, xform_ty, body);
        lam_over(k, I_FV, nat, body)
    };

    let i = k.fvar(I_FV);
    let v = k.fvar(V_FV);
    let j = k.fvar(J_FV);
    let rec = k.const_(lg.nat_rec, vec![l1]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let body = t_app(k, outer, &[v, j]);
    let value = lam_over(k, J_FV, nat, body);
    let value = lam_over(k, V_FV, fam_ty, value);
    let value = lam_over(k, I_FV, nat, value);
    let value = lam_over(k, AL_FV, ty1, value);

    let ty = {
        let inner = arrow(k, nat, al);
        let inner = arrow(k, fam_ty, inner);
        let inner = arrow(k, nat, inner);
        pi_over(k, AL_FV, ty1, inner)
    };

    let name = k.name_str(ns, "removeAt");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Index.insertAt : forall (a : Type), Nat -> a -> (Nat -> a) -> Nat -> a`.
///
/// `insertAt a i w v` puts `w` at index `i` and shifts every index from `i`
/// upward by one. Same recursion shape as [`declare_remove_at`], with the
/// inserted value carried through the motive.
fn declare_insert_at(k: &mut Kernel, lg: &LogicPrelude, ns: NameId) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let ty1 = k.sort(l1);
    let nat = k.const_(lg.nat, vec![]);
    let nat_zero = k.const_(lg.nat_zero, vec![]);
    let nat_succ = k.const_(lg.nat_succ, vec![]);

    let al = k.fvar(AL_FV);
    let fam_ty = arrow(k, nat, al);
    let xform_ty = {
        let inner = arrow(k, fam_ty, fam_ty);
        arrow(k, al, inner)
    };

    let motive = lam_over(k, SCRATCH_FV, nat, xform_ty);
    let minor_zero = {
        let w = k.fvar(W_FV);
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let inner_motive = lam_over(k, SCRATCH_FV, nat, al);
        let inner_succ = {
            let jp = k.fvar(T_FV);
            let body = k.app(v, jp);
            let body = lam_over(k, SCRATCH_FV, al, body);
            lam_over(k, T_FV, nat, body)
        };
        let rec = k.const_(lg.nat_rec, vec![l1]);
        let body = t_app(k, rec, &[inner_motive, w, inner_succ, j]);
        let body = lam_over(k, J_FV, nat, body);
        let body = lam_over(k, V_FV, fam_ty, body);
        lam_over(k, W_FV, al, body)
    };
    let minor_succ = {
        let ih = k.fvar(IH_FV);
        let w = k.fvar(W_FV);
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let inner_motive = lam_over(k, SCRATCH_FV, nat, al);
        let inner_zero = k.app(v, nat_zero);
        let inner_succ = {
            let jp = k.fvar(T_FV);
            let shifted = {
                let t = k.fvar(N_FV);
                let st = k.app(nat_succ, t);
                let b = k.app(v, st);
                lam_over(k, N_FV, nat, b)
            };
            let body = t_app(k, ih, &[w, shifted, jp]);
            let body = lam_over(k, SCRATCH_FV, al, body);
            lam_over(k, T_FV, nat, body)
        };
        let rec = k.const_(lg.nat_rec, vec![l1]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, j]);
        let body = lam_over(k, J_FV, nat, body);
        let body = lam_over(k, V_FV, fam_ty, body);
        let body = lam_over(k, W_FV, al, body);
        let body = lam_over(k, IH_FV, xform_ty, body);
        lam_over(k, I_FV, nat, body)
    };

    let i = k.fvar(I_FV);
    let w = k.fvar(W_FV);
    let v = k.fvar(V_FV);
    let j = k.fvar(J_FV);
    let rec = k.const_(lg.nat_rec, vec![l1]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let body = t_app(k, outer, &[w, v, j]);
    let value = lam_over(k, J_FV, nat, body);
    let value = lam_over(k, V_FV, fam_ty, value);
    let value = lam_over(k, W_FV, al, value);
    let value = lam_over(k, I_FV, nat, value);
    let value = lam_over(k, AL_FV, ty1, value);

    let ty = {
        let inner = arrow(k, nat, al);
        let inner = arrow(k, fam_ty, inner);
        let inner = arrow(k, al, inner);
        let inner = arrow(k, nat, inner);
        pi_over(k, AL_FV, ty1, inner)
    };

    let name = k.name_str(ns, "insertAt");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

/// Every name this module declares.
///
/// The accessor is `owned_names` and not `all`/`names`/`iter`: a generic
/// method name on a prelude `*Names` struct puts this content file into
/// `scripts/check-kernel-trusted-core.py`'s trusted closure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndexNames {
    pub le: NameId,
    pub remove_at: NameId,
    pub insert_at: NameId,
}

/// `#[cfg(test)]` for the same reason `ModuleNames::all` is: these names are
/// deliberately not threaded into `NatPrelude`.
#[cfg(test)]
impl IndexNames {
    #[must_use]
    pub fn owned_names(&self) -> [NameId; 3] {
        [self.le, self.remove_at, self.insert_at]
    }
}

/// Declare `AlgS.Index.*`. Needs only the logic prelude, so it can sit
/// anywhere at or after the `AlgS` root is interned.
pub(crate) fn declare_index_surgery(
    k: &mut Kernel,
    lg: &LogicPrelude,
    algs: NameId,
) -> Result<IndexNames, KernelError> {
    let ns = k.name_str(algs, "Index");
    let le = declare_le(k, lg, ns)?;
    let remove_at = declare_remove_at(k, lg, ns)?;
    let insert_at = declare_insert_at(k, lg, ns)?;
    Ok(IndexNames {
        le,
        remove_at,
        insert_at,
    })
}

#[cfg(test)]
#[path = "vector_space_exchange_tests.rs"]
mod vector_space_exchange_tests;
