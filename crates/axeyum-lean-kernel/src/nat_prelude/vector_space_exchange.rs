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

use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

use super::structures::{app2, arrow, eq_of, lam_over, pi_over, refl_of};

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
const H1_FV: u64 = 26_010;
const H2_FV: u64 = 26_011;
const SHIFT_FV: u64 = 26_020;
const CONGR_FV: u64 = 26_021;
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
// Shared term builders for the lemmas below.
// ---------------------------------------------------------------------------

/// `fun t : Nat => v (Nat.succ t)` — the family `v` shifted down by one, the
/// argument every recursive call in this file is made at.
fn shift(k: &mut Kernel, nat: ExprId, nat_succ: ExprId, v: ExprId) -> ExprId {
    let t = k.fvar(SHIFT_FV);
    let st = k.app(nat_succ, t);
    let b = k.app(v, st);
    lam_over(k, SHIFT_FV, nat, b)
}

/// `Eq Nat (Nat.succ a) (Nat.succ b)` from `h : Eq Nat a b`, by `Eq.rec` with
/// the motive `fun x _ => Eq Nat (succ a) (succ x)`. There is no `congrArg`
/// in [`LogicPrelude`] — only `congr_fun_prime`, which varies the FUNCTION —
/// so the argument-side congruence is built here.
fn congr_succ(
    k: &mut Kernel,
    lg: &LogicPrelude,
    nat: ExprId,
    nat_succ: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sa = k.app(nat_succ, a);
    let motive = {
        let x = k.fvar(CONGR_FV);
        let sx = k.app(nat_succ, x);
        let concl = eq_of(k, lg, l1, nat, sa, sx);
        let hyp = eq_of(k, lg, l1, nat, a, x);
        let anon = k.anon();
        let inner = k.lam(anon, hyp, concl, BinderInfo::Default);
        lam_over(k, CONGR_FV, nat, inner)
    };
    let base = refl_of(k, lg, l1, nat, sa);
    let rec = k.const_(lg.eq_rec, vec![l0, l1]);
    t_app(k, rec, &[nat, a, motive, base, b, h])
}

/// `False.rec` at a `Prop` goal, taking the refutation at whatever type is
/// definitionally `False` — `le (succ i) Nat.zero` is, by ι.
fn ex_falso(k: &mut Kernel, lg: &LogicPrelude, goal: ExprId, h: ExprId) -> ExprId {
    let l0 = k.level_zero();
    let false_ty = k.const_(lg.false_, vec![]);
    let motive = lam_over(k, SCRATCH_FV, false_ty, goal);
    let rec = k.const_(lg.false_rec, vec![l0]);
    t_app(k, rec, &[motive, h])
}

/// The three `AlgS.Index` constants with their application helpers.
struct IxCtx {
    nat: ExprId,
    nat_zero: ExprId,
    nat_succ: ExprId,
    le: NameId,
    remove_at: NameId,
    insert_at: NameId,
}

impl IxCtx {
    fn new(
        k: &mut Kernel,
        lg: &LogicPrelude,
        le: NameId,
        remove_at: NameId,
        insert_at: NameId,
    ) -> Self {
        IxCtx {
            nat: k.const_(lg.nat, vec![]),
            nat_zero: k.const_(lg.nat_zero, vec![]),
            nat_succ: k.const_(lg.nat_succ, vec![]),
            le,
            remove_at,
            insert_at,
        }
    }
    fn succ(&self, k: &mut Kernel, x: ExprId) -> ExprId {
        k.app(self.nat_succ, x)
    }
    fn le_at(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        let c = k.const_(self.le, vec![]);
        t_app(k, c, &[a, b])
    }
    fn rem(&self, k: &mut Kernel, al: ExprId, i: ExprId, v: ExprId, j: ExprId) -> ExprId {
        let c = k.const_(self.remove_at, vec![]);
        t_app(k, c, &[al, i, v, j])
    }
    /// `insertAt al i w v` — a family (`Nat -> al`), not yet indexed.
    fn ins_fam(&self, k: &mut Kernel, al: ExprId, i: ExprId, w: ExprId, v: ExprId) -> ExprId {
        let c = k.const_(self.insert_at, vec![]);
        t_app(k, c, &[al, i, w, v])
    }
    fn ins(
        &self,
        k: &mut Kernel,
        al: ExprId,
        i: ExprId,
        w: ExprId,
        v: ExprId,
        j: ExprId,
    ) -> ExprId {
        let f = self.ins_fam(k, al, i, w, v);
        k.app(f, j)
    }
}

// ---------------------------------------------------------------------------
// The `AlgS.Index.le` lemmas.
// ---------------------------------------------------------------------------

/// `AlgS.Index.le_zero_eq : forall i, le i Nat.zero -> Eq Nat i Nat.zero`.
///
/// `Nat.rec` on `i`: at zero the conclusion is `Eq.refl`; at `succ i'` the
/// hypothesis IS `False` by ι, so the goal is ex falso.
fn declare_le_zero_eq(
    k: &mut Kernel,
    lg: &LogicPrelude,
    c: &IxCtx,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let nat = c.nat;
    let zero = c.nat_zero;

    let motive = {
        let i = k.fvar(I_FV);
        let hyp = c.le_at(k, i, zero);
        let concl = eq_of(k, lg, l1, nat, i, zero);
        let body = arrow(k, hyp, concl);
        lam_over(k, I_FV, nat, body)
    };
    let minor_zero = {
        let hyp = c.le_at(k, zero, zero);
        let r = refl_of(k, lg, l1, nat, zero);
        lam_over(k, SCRATCH_FV, hyp, r)
    };
    let minor_succ = {
        let ip = k.fvar(I_FV);
        let sip = c.succ(k, ip);
        let ih_ty = {
            let hyp = c.le_at(k, ip, zero);
            let concl = eq_of(k, lg, l1, nat, ip, zero);
            arrow(k, hyp, concl)
        };
        let hyp = c.le_at(k, sip, zero);
        let h = k.fvar(H1_FV);
        let goal = eq_of(k, lg, l1, nat, sip, zero);
        let body = ex_falso(k, lg, goal, h);
        let body = lam_over(k, H1_FV, hyp, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, nat, body)
    };
    let i = k.fvar(I_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let body = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let value = lam_over(k, I_FV, nat, body);

    let ty = {
        let hyp = c.le_at(k, i, zero);
        let concl = eq_of(k, lg, l1, nat, i, zero);
        let body = arrow(k, hyp, concl);
        pi_over(k, I_FV, nat, body)
    };

    let name = k.name_str(ns, "le_zero_eq");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Index.le_refl : forall n, le n n`.
fn declare_le_refl(
    k: &mut Kernel,
    lg: &LogicPrelude,
    c: &IxCtx,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let nat = c.nat;

    let motive = {
        let n = k.fvar(N_FV);
        let body = c.le_at(k, n, n);
        lam_over(k, N_FV, nat, body)
    };
    let minor_zero = k.const_(lg.true_intro, vec![]);
    let minor_succ = {
        let n = k.fvar(N_FV);
        let ih_ty = c.le_at(k, n, n);
        let ih = k.fvar(IH_FV);
        // `le (succ n) (succ n)` ι-reduces to `le n n`, so the induction
        // hypothesis IS the goal.
        let body = lam_over(k, IH_FV, ih_ty, ih);
        lam_over(k, N_FV, nat, body)
    };
    let n = k.fvar(N_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let body = t_app(k, rec, &[motive, minor_zero, minor_succ, n]);
    let value = lam_over(k, N_FV, nat, body);

    let ty = {
        let body = c.le_at(k, n, n);
        pi_over(k, N_FV, nat, body)
    };

    let name = k.name_str(ns, "le_refl");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Index.le_dichotomy : forall m n, Or (le m n) (le (Nat.succ n) m)`.
///
/// Totality of the order, and the only route from a REFUTED `le (succ n) m`
/// back to `le m n`: this shelf has no `Decidable` instance for `le`, so the
/// contrapositive form of the exchange bound has to be resolved through a
/// constructive `Or`.
fn declare_le_dichotomy(
    k: &mut Kernel,
    lg: &LogicPrelude,
    c: &IxCtx,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let nat = c.nat;

    let goal_at = |k: &mut Kernel, m: ExprId, n: ExprId| {
        let a = c.le_at(k, m, n);
        let sn = c.succ(k, n);
        let b = c.le_at(k, sn, m);
        let or_c = k.const_(lg.or, vec![]);
        let g = app2(k, or_c, a, b);
        (a, b, g)
    };

    let motive = {
        let m = k.fvar(N_FV);
        let n = k.fvar(J_FV);
        let (_, _, g) = goal_at(k, m, n);
        let body = pi_over(k, J_FV, nat, g);
        lam_over(k, N_FV, nat, body)
    };
    let minor_zero = {
        let n = k.fvar(J_FV);
        let (a, b, _) = goal_at(k, c.nat_zero, n);
        let ti = k.const_(lg.true_intro, vec![]);
        let inl = k.const_(lg.or_inl, vec![]);
        let body = t_app(k, inl, &[a, b, ti]);
        lam_over(k, J_FV, nat, body)
    };
    let minor_succ = {
        let mp = k.fvar(N_FV);
        let smp = c.succ(k, mp);
        let ih_ty = {
            let n = k.fvar(J_FV);
            let (_, _, g) = goal_at(k, mp, n);
            pi_over(k, J_FV, nat, g)
        };
        let ih = k.fvar(IH_FV);
        let inner_motive = {
            let n = k.fvar(J_FV);
            let (_, _, g) = goal_at(k, smp, n);
            lam_over(k, J_FV, nat, g)
        };
        let inner_zero = {
            let (a, b, _) = goal_at(k, smp, c.nat_zero);
            // `le (succ zero) (succ m') ≡ le zero m' ≡ True`.
            let ti = k.const_(lg.true_intro, vec![]);
            let inr = k.const_(lg.or_inr, vec![]);
            t_app(k, inr, &[a, b, ti])
        };
        let inner_succ = {
            let np = k.fvar(J_FV);
            let (_, _, g) = goal_at(k, smp, np);
            // `Or (le (succ m') (succ n')) (le (succ (succ n')) (succ m'))`
            // ι-reduces to `Or (le m' n') (le (succ n') m')`, which is
            // exactly `ih n'`.
            let body = k.app(ih, np);
            let body = lam_over(k, SCRATCH_FV, g, body);
            lam_over(k, J_FV, nat, body)
        };
        let n = k.fvar(J_FV);
        let rec = k.const_(lg.nat_rec, vec![l0]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, n]);
        let body = lam_over(k, J_FV, nat, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, N_FV, nat, body)
    };
    let m = k.fvar(N_FV);
    let n = k.fvar(J_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, m]);
    let body = k.app(outer, n);
    let value = lam_over(k, J_FV, nat, body);
    let value = lam_over(k, N_FV, nat, value);

    let ty = {
        let (_, _, g) = goal_at(k, m, n);
        let body = pi_over(k, J_FV, nat, g);
        pi_over(k, N_FV, nat, body)
    };

    let name = k.name_str(ns, "le_dichotomy");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Index.le_succ_cases : forall i n, le i (Nat.succ n) ->
/// Or (le i n) (Eq Nat i (Nat.succ n))`.
///
/// The boundary split the exchange induction runs on: an index bounded by
/// `succ n` is either bounded by `n` or IS `succ n`. `Nat.rec` on `i`, with a
/// second `Nat.rec` on `n` inside the successor branch — the inner recursive
/// value is never used, only the OUTER induction hypothesis at `n'`.
fn declare_le_succ_cases(
    k: &mut Kernel,
    lg: &LogicPrelude,
    c: &IxCtx,
    le_zero_eq: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let nat = c.nat;

    // `(hypothesis, left disjunct, right disjunct, goal)` at `i`, `n`.
    let parts = |k: &mut Kernel, i: ExprId, n: ExprId| {
        let sn = c.succ(k, n);
        let hyp = c.le_at(k, i, sn);
        let left = c.le_at(k, i, n);
        let right = eq_of(k, lg, l1, nat, i, sn);
        let or_c = k.const_(lg.or, vec![]);
        let goal = app2(k, or_c, left, right);
        (hyp, left, right, goal)
    };

    let motive = {
        let i = k.fvar(I_FV);
        let n = k.fvar(J_FV);
        let (hyp, _, _, goal) = parts(k, i, n);
        let body = arrow(k, hyp, goal);
        let body = pi_over(k, J_FV, nat, body);
        lam_over(k, I_FV, nat, body)
    };
    let minor_zero = {
        let n = k.fvar(J_FV);
        let (hyp, left, right, _) = parts(k, c.nat_zero, n);
        // `le zero n ≡ True`, so `True.intro` inhabits the left disjunct.
        let ti = k.const_(lg.true_intro, vec![]);
        let inl = k.const_(lg.or_inl, vec![]);
        let body = t_app(k, inl, &[left, right, ti]);
        let body = lam_over(k, SCRATCH_FV, hyp, body);
        lam_over(k, J_FV, nat, body)
    };
    let minor_succ = {
        let ip = k.fvar(I_FV);
        let sip = c.succ(k, ip);
        let ih_ty = {
            let n = k.fvar(J_FV);
            let (hyp, _, _, goal) = parts(k, ip, n);
            let body = arrow(k, hyp, goal);
            pi_over(k, J_FV, nat, body)
        };
        let ih = k.fvar(IH_FV);

        let inner_motive = {
            let n = k.fvar(J_FV);
            let (hyp, _, _, goal) = parts(k, sip, n);
            let body = arrow(k, hyp, goal);
            lam_over(k, J_FV, nat, body)
        };
        let inner_zero = {
            let (hyp, left, right, _) = parts(k, sip, c.nat_zero);
            let h = k.fvar(H1_FV);
            // `h : le (succ i') (succ zero) ≡ le i' zero`, so `le_zero_eq`
            // pins `i' = zero` and `succ` congruence lifts it.
            let lz = {
                let t = k.const_(le_zero_eq, vec![]);
                t_app(k, t, &[ip, h])
            };
            let eqn = congr_succ(k, lg, nat, c.nat_succ, ip, c.nat_zero, lz);
            let inr = k.const_(lg.or_inr, vec![]);
            let body = t_app(k, inr, &[left, right, eqn]);
            lam_over(k, H1_FV, hyp, body)
        };
        let inner_succ = {
            let np = k.fvar(J_FV);
            let snp = c.succ(k, np);
            let (hyp, left, right, goal) = parts(k, sip, snp);
            let (_, ih_left, ih_right, _) = parts(k, ip, np);
            let inner_ih_ty = {
                let (h2, _, _, g2) = parts(k, sip, np);
                arrow(k, h2, g2)
            };
            let h = k.fvar(H1_FV);
            let ih_at = {
                let e = k.app(ih, np);
                k.app(e, h)
            };
            let on_left = {
                let hl = k.fvar(H2_FV);
                let inl = k.const_(lg.or_inl, vec![]);
                // `le i' n'` IS `le (succ i') (succ n')` by ι.
                let b = t_app(k, inl, &[left, right, hl]);
                lam_over(k, H2_FV, ih_left, b)
            };
            let on_right = {
                let hr = k.fvar(H2_FV);
                let eqn = congr_succ(k, lg, nat, c.nat_succ, ip, snp, hr);
                let inr = k.const_(lg.or_inr, vec![]);
                let b = t_app(k, inr, &[left, right, eqn]);
                lam_over(k, H2_FV, ih_right, b)
            };
            let elim = k.const_(lg.or_elim, vec![]);
            let body = t_app(
                k,
                elim,
                &[ih_left, ih_right, goal, ih_at, on_left, on_right],
            );
            let body = lam_over(k, H1_FV, hyp, body);
            let body = lam_over(k, SCRATCH_FV, inner_ih_ty, body);
            lam_over(k, J_FV, nat, body)
        };
        let n = k.fvar(J_FV);
        let rec = k.const_(lg.nat_rec, vec![l0]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, n]);
        let body = lam_over(k, J_FV, nat, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, nat, body)
    };
    let i = k.fvar(I_FV);
    let n = k.fvar(J_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let body = k.app(outer, n);
    let value = lam_over(k, J_FV, nat, body);
    let value = lam_over(k, I_FV, nat, value);

    let ty = {
        let (hyp, _, _, goal) = parts(k, i, n);
        let body = arrow(k, hyp, goal);
        let body = pi_over(k, J_FV, nat, body);
        pi_over(k, I_FV, nat, body)
    };

    let name = k.name_str(ns, "le_succ_cases");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// The family-surgery lemmas.
// ---------------------------------------------------------------------------

/// `AlgS.Index.insertAt_at : forall (a : Type) (w : a) (i : Nat)
/// (v : Nat -> a), Eq a (insertAt a i w v i) w`.
///
/// The inserted value sits at the index it was inserted at.
fn declare_insert_at_at(
    k: &mut Kernel,
    lg: &LogicPrelude,
    c: &IxCtx,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let ty1 = k.sort(l1);
    let nat = c.nat;
    let al = k.fvar(AL_FV);
    let fam_ty = arrow(k, nat, al);
    let w = k.fvar(W_FV);

    let motive = {
        let i = k.fvar(I_FV);
        let v = k.fvar(V_FV);
        let lhs = c.ins(k, al, i, w, v, i);
        let concl = eq_of(k, lg, l1, al, lhs, w);
        let body = pi_over(k, V_FV, fam_ty, concl);
        lam_over(k, I_FV, nat, body)
    };
    let minor_zero = {
        let r = refl_of(k, lg, l1, al, w);
        lam_over(k, V_FV, fam_ty, r)
    };
    let minor_succ = {
        let ip = k.fvar(I_FV);
        let ih_ty = {
            let v = k.fvar(V_FV);
            let lhs = c.ins(k, al, ip, w, v, ip);
            let concl = eq_of(k, lg, l1, al, lhs, w);
            pi_over(k, V_FV, fam_ty, concl)
        };
        let ih = k.fvar(IH_FV);
        let v = k.fvar(V_FV);
        let sv = shift(k, nat, c.nat_succ, v);
        let body = k.app(ih, sv);
        let body = lam_over(k, V_FV, fam_ty, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, nat, body)
    };
    let i = k.fvar(I_FV);
    let v = k.fvar(V_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let body = k.app(outer, v);
    let value = lam_over(k, V_FV, fam_ty, body);
    let value = lam_over(k, I_FV, nat, value);
    let value = lam_over(k, W_FV, al, value);
    let value = lam_over(k, AL_FV, ty1, value);

    let ty = {
        let lhs = c.ins(k, al, i, w, v, i);
        let concl = eq_of(k, lg, l1, al, lhs, w);
        let body = pi_over(k, V_FV, fam_ty, concl);
        let body = pi_over(k, I_FV, nat, body);
        let body = pi_over(k, W_FV, al, body);
        pi_over(k, AL_FV, ty1, body)
    };

    let name = k.name_str(ns, "insertAt_at");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Index.insertAt_below : forall (a : Type) (w : a) (i : Nat)
/// (v : Nat -> a) (j : Nat), le (Nat.succ j) i ->
/// Eq a (insertAt a i w v j) (v j)`.
///
/// Strictly below the insertion point the family is untouched.
fn declare_insert_at_below(
    k: &mut Kernel,
    lg: &LogicPrelude,
    c: &IxCtx,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let ty1 = k.sort(l1);
    let nat = c.nat;
    let al = k.fvar(AL_FV);
    let fam_ty = arrow(k, nat, al);
    let w = k.fvar(W_FV);

    let stmt = |k: &mut Kernel, i: ExprId, v: ExprId, j: ExprId| {
        let sj = c.succ(k, j);
        let hyp = c.le_at(k, sj, i);
        let lhs = c.ins(k, al, i, w, v, j);
        let rhs = k.app(v, j);
        let concl = eq_of(k, lg, l1, al, lhs, rhs);
        (hyp, concl)
    };

    let motive = {
        let i = k.fvar(I_FV);
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let (hyp, concl) = stmt(k, i, v, j);
        let body = arrow(k, hyp, concl);
        let body = pi_over(k, J_FV, nat, body);
        let body = pi_over(k, V_FV, fam_ty, body);
        lam_over(k, I_FV, nat, body)
    };
    let minor_zero = {
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let (hyp, concl) = stmt(k, c.nat_zero, v, j);
        let h = k.fvar(H1_FV);
        // `le (succ j) zero ≡ False`.
        let body = ex_falso(k, lg, concl, h);
        let body = lam_over(k, H1_FV, hyp, body);
        let body = lam_over(k, J_FV, nat, body);
        lam_over(k, V_FV, fam_ty, body)
    };
    let minor_succ = {
        let ip = k.fvar(I_FV);
        let sip = c.succ(k, ip);
        let ih_ty = {
            let v = k.fvar(V_FV);
            let j = k.fvar(J_FV);
            let (hyp, concl) = stmt(k, ip, v, j);
            let body = arrow(k, hyp, concl);
            let body = pi_over(k, J_FV, nat, body);
            pi_over(k, V_FV, fam_ty, body)
        };
        let ih = k.fvar(IH_FV);
        let v = k.fvar(V_FV);

        let inner_motive = {
            let j = k.fvar(J_FV);
            let (hyp, concl) = stmt(k, sip, v, j);
            let body = arrow(k, hyp, concl);
            lam_over(k, J_FV, nat, body)
        };
        let inner_zero = {
            let (hyp, _) = stmt(k, sip, v, c.nat_zero);
            let vz = k.app(v, c.nat_zero);
            // `insertAt (succ i') w v zero ≡ v zero`.
            let r = refl_of(k, lg, l1, al, vz);
            lam_over(k, H1_FV, hyp, r)
        };
        let inner_succ = {
            let jp = k.fvar(J_FV);
            let sjp = c.succ(k, jp);
            let (hyp, _) = stmt(k, sip, v, sjp);
            let inner_ih_ty = {
                let (h2, c2) = stmt(k, sip, v, jp);
                arrow(k, h2, c2)
            };
            let h = k.fvar(H1_FV);
            let sv = shift(k, nat, c.nat_succ, v);
            let body = {
                let e = k.app(ih, sv);
                let e = k.app(e, jp);
                k.app(e, h)
            };
            let body = lam_over(k, H1_FV, hyp, body);
            let body = lam_over(k, SCRATCH_FV, inner_ih_ty, body);
            lam_over(k, J_FV, nat, body)
        };
        let j = k.fvar(J_FV);
        let rec = k.const_(lg.nat_rec, vec![l0]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, j]);
        let body = lam_over(k, J_FV, nat, body);
        let body = lam_over(k, V_FV, fam_ty, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, nat, body)
    };

    let i = k.fvar(I_FV);
    let v = k.fvar(V_FV);
    let j = k.fvar(J_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let body = t_app(k, outer, &[v, j]);
    let value = lam_over(k, J_FV, nat, body);
    let value = lam_over(k, V_FV, fam_ty, value);
    let value = lam_over(k, I_FV, nat, value);
    let value = lam_over(k, W_FV, al, value);
    let value = lam_over(k, AL_FV, ty1, value);

    let ty = {
        let (hyp, concl) = stmt(k, i, v, j);
        let body = arrow(k, hyp, concl);
        let body = pi_over(k, J_FV, nat, body);
        let body = pi_over(k, V_FV, fam_ty, body);
        let body = pi_over(k, I_FV, nat, body);
        let body = pi_over(k, W_FV, al, body);
        pi_over(k, AL_FV, ty1, body)
    };

    let name = k.name_str(ns, "insertAt_below");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Index.insertAt_above : forall (a : Type) (w : a) (i : Nat)
/// (v : Nat -> a) (j : Nat), le i j ->
/// Eq a (insertAt a i w v (Nat.succ j)) (v j)`.
///
/// At and above the insertion point the family reappears, shifted up by one.
/// Together with [`declare_insert_at_at`] and [`declare_insert_at_below`]
/// this pins `insertAt` at every index.
fn declare_insert_at_above(
    k: &mut Kernel,
    lg: &LogicPrelude,
    c: &IxCtx,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let ty1 = k.sort(l1);
    let nat = c.nat;
    let al = k.fvar(AL_FV);
    let fam_ty = arrow(k, nat, al);
    let w = k.fvar(W_FV);

    let stmt = |k: &mut Kernel, i: ExprId, v: ExprId, j: ExprId| {
        let hyp = c.le_at(k, i, j);
        let sj = c.succ(k, j);
        let lhs = c.ins(k, al, i, w, v, sj);
        let rhs = k.app(v, j);
        let concl = eq_of(k, lg, l1, al, lhs, rhs);
        (hyp, concl)
    };

    let motive = {
        let i = k.fvar(I_FV);
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let (hyp, concl) = stmt(k, i, v, j);
        let body = arrow(k, hyp, concl);
        let body = pi_over(k, J_FV, nat, body);
        let body = pi_over(k, V_FV, fam_ty, body);
        lam_over(k, I_FV, nat, body)
    };
    let minor_zero = {
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let (hyp, _) = stmt(k, c.nat_zero, v, j);
        let vj = k.app(v, j);
        // `insertAt zero w v (succ j) ≡ v j`; the hypothesis is not used.
        let r = refl_of(k, lg, l1, al, vj);
        let body = lam_over(k, H1_FV, hyp, r);
        let body = lam_over(k, J_FV, nat, body);
        lam_over(k, V_FV, fam_ty, body)
    };
    let minor_succ = {
        let ip = k.fvar(I_FV);
        let sip = c.succ(k, ip);
        let ih_ty = {
            let v = k.fvar(V_FV);
            let j = k.fvar(J_FV);
            let (hyp, concl) = stmt(k, ip, v, j);
            let body = arrow(k, hyp, concl);
            let body = pi_over(k, J_FV, nat, body);
            pi_over(k, V_FV, fam_ty, body)
        };
        let ih = k.fvar(IH_FV);
        let v = k.fvar(V_FV);

        let inner_motive = {
            let j = k.fvar(J_FV);
            let (hyp, concl) = stmt(k, sip, v, j);
            let body = arrow(k, hyp, concl);
            lam_over(k, J_FV, nat, body)
        };
        let inner_zero = {
            let (hyp, concl) = stmt(k, sip, v, c.nat_zero);
            let h = k.fvar(H1_FV);
            // `le (succ i') zero ≡ False`.
            let body = ex_falso(k, lg, concl, h);
            lam_over(k, H1_FV, hyp, body)
        };
        let inner_succ = {
            let jp = k.fvar(J_FV);
            let sjp = c.succ(k, jp);
            let (hyp, _) = stmt(k, sip, v, sjp);
            let inner_ih_ty = {
                let (h2, c2) = stmt(k, sip, v, jp);
                arrow(k, h2, c2)
            };
            let h = k.fvar(H1_FV);
            let sv = shift(k, nat, c.nat_succ, v);
            let body = {
                let e = k.app(ih, sv);
                let e = k.app(e, jp);
                k.app(e, h)
            };
            let body = lam_over(k, H1_FV, hyp, body);
            let body = lam_over(k, SCRATCH_FV, inner_ih_ty, body);
            lam_over(k, J_FV, nat, body)
        };
        let j = k.fvar(J_FV);
        let rec = k.const_(lg.nat_rec, vec![l0]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, j]);
        let body = lam_over(k, J_FV, nat, body);
        let body = lam_over(k, V_FV, fam_ty, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, nat, body)
    };

    let i = k.fvar(I_FV);
    let v = k.fvar(V_FV);
    let j = k.fvar(J_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let body = t_app(k, outer, &[v, j]);
    let value = lam_over(k, J_FV, nat, body);
    let value = lam_over(k, V_FV, fam_ty, value);
    let value = lam_over(k, I_FV, nat, value);
    let value = lam_over(k, W_FV, al, value);
    let value = lam_over(k, AL_FV, ty1, value);

    let ty = {
        let (hyp, concl) = stmt(k, i, v, j);
        let body = arrow(k, hyp, concl);
        let body = pi_over(k, J_FV, nat, body);
        let body = pi_over(k, V_FV, fam_ty, body);
        let body = pi_over(k, I_FV, nat, body);
        let body = pi_over(k, W_FV, al, body);
        pi_over(k, AL_FV, ty1, body)
    };

    let name = k.name_str(ns, "insertAt_above");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Index.removeAt_insertAt : forall (a : Type) (w : a) (i : Nat)
/// (v : Nat -> a) (j : Nat),
/// Eq a (removeAt a i (insertAt a i w v) j) (v j)`.
///
/// **The surgery is invertible.** Deleting the index you just inserted at
/// returns the original family, pointwise, with no side condition at all —
/// the two recursions run in lock step and the successor step is the
/// induction hypothesis at the shifted family, up to η.
fn declare_remove_at_insert_at(
    k: &mut Kernel,
    lg: &LogicPrelude,
    c: &IxCtx,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let ty1 = k.sort(l1);
    let nat = c.nat;
    let al = k.fvar(AL_FV);
    let fam_ty = arrow(k, nat, al);
    let w = k.fvar(W_FV);

    let stmt = |k: &mut Kernel, i: ExprId, v: ExprId, j: ExprId| {
        let ins = c.ins_fam(k, al, i, w, v);
        let lhs = c.rem(k, al, i, ins, j);
        let rhs = k.app(v, j);
        eq_of(k, lg, l1, al, lhs, rhs)
    };

    let motive = {
        let i = k.fvar(I_FV);
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let concl = stmt(k, i, v, j);
        let body = pi_over(k, J_FV, nat, concl);
        let body = pi_over(k, V_FV, fam_ty, body);
        lam_over(k, I_FV, nat, body)
    };
    let minor_zero = {
        let v = k.fvar(V_FV);
        let j = k.fvar(J_FV);
        let vj = k.app(v, j);
        // `removeAt zero (insertAt zero w v) j ≡ insertAt zero w v (succ j)
        //  ≡ v j`.
        let r = refl_of(k, lg, l1, al, vj);
        let body = lam_over(k, J_FV, nat, r);
        lam_over(k, V_FV, fam_ty, body)
    };
    let minor_succ = {
        let ip = k.fvar(I_FV);
        let sip = c.succ(k, ip);
        let ih_ty = {
            let v = k.fvar(V_FV);
            let j = k.fvar(J_FV);
            let concl = stmt(k, ip, v, j);
            let body = pi_over(k, J_FV, nat, concl);
            pi_over(k, V_FV, fam_ty, body)
        };
        let ih = k.fvar(IH_FV);
        let v = k.fvar(V_FV);

        let inner_motive = {
            let j = k.fvar(J_FV);
            let concl = stmt(k, sip, v, j);
            lam_over(k, J_FV, nat, concl)
        };
        let inner_zero = {
            let vz = k.app(v, c.nat_zero);
            refl_of(k, lg, l1, al, vz)
        };
        let inner_succ = {
            let jp = k.fvar(J_FV);
            let inner_ih_ty = stmt(k, sip, v, jp);
            let sv = shift(k, nat, c.nat_succ, v);
            let body = {
                let e = k.app(ih, sv);
                k.app(e, jp)
            };
            let body = lam_over(k, SCRATCH_FV, inner_ih_ty, body);
            lam_over(k, J_FV, nat, body)
        };
        let j = k.fvar(J_FV);
        let rec = k.const_(lg.nat_rec, vec![l0]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, j]);
        let body = lam_over(k, J_FV, nat, body);
        let body = lam_over(k, V_FV, fam_ty, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, nat, body)
    };

    let i = k.fvar(I_FV);
    let v = k.fvar(V_FV);
    let j = k.fvar(J_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let body = t_app(k, outer, &[v, j]);
    let value = lam_over(k, J_FV, nat, body);
    let value = lam_over(k, V_FV, fam_ty, value);
    let value = lam_over(k, I_FV, nat, value);
    let value = lam_over(k, W_FV, al, value);
    let value = lam_over(k, AL_FV, ty1, value);

    let ty = {
        let concl = stmt(k, i, v, j);
        let body = pi_over(k, J_FV, nat, concl);
        let body = pi_over(k, V_FV, fam_ty, body);
        let body = pi_over(k, I_FV, nat, body);
        let body = pi_over(k, W_FV, al, body);
        pi_over(k, AL_FV, ty1, body)
    };

    let name = k.name_str(ns, "removeAt_insertAt");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
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
    pub le_zero_eq: NameId,
    pub le_refl: NameId,
    pub le_dichotomy: NameId,
    pub le_succ_cases: NameId,
    pub insert_at_at: NameId,
    pub insert_at_below: NameId,
    pub insert_at_above: NameId,
    pub remove_at_insert_at: NameId,
}

/// `#[cfg(test)]` for the same reason `ModuleNames::all` is: these names are
/// deliberately not threaded into `NatPrelude`.
#[cfg(test)]
impl IndexNames {
    #[must_use]
    pub fn owned_names(&self) -> [NameId; 11] {
        [
            self.le,
            self.remove_at,
            self.insert_at,
            self.le_zero_eq,
            self.le_refl,
            self.le_dichotomy,
            self.le_succ_cases,
            self.insert_at_at,
            self.insert_at_below,
            self.insert_at_above,
            self.remove_at_insert_at,
        ]
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
    let c = IxCtx::new(k, lg, le, remove_at, insert_at);
    let le_zero_eq = declare_le_zero_eq(k, lg, &c, ns)?;
    let le_refl = declare_le_refl(k, lg, &c, ns)?;
    let le_dichotomy = declare_le_dichotomy(k, lg, &c, ns)?;
    let le_succ_cases = declare_le_succ_cases(k, lg, &c, le_zero_eq, ns)?;
    let insert_at_at = declare_insert_at_at(k, lg, &c, ns)?;
    let insert_at_below = declare_insert_at_below(k, lg, &c, ns)?;
    let insert_at_above = declare_insert_at_above(k, lg, &c, ns)?;
    let remove_at_insert_at = declare_remove_at_insert_at(k, lg, &c, ns)?;
    Ok(IndexNames {
        le,
        remove_at,
        insert_at,
        le_zero_eq,
        le_refl,
        le_dichotomy,
        le_succ_cases,
        insert_at_at,
        insert_at_below,
        insert_at_above,
        remove_at_insert_at,
    })
}

#[cfg(test)]
#[path = "vector_space_exchange_tests.rs"]
mod vector_space_exchange_tests;
