//! Proof steps that were written once per file, unified into one copy each.
//!
//! WHY THIS MODULE EXISTS. These are *inline unnamed proof steps*: they build a
//! proof term and declare nothing, so the kernel environment never learns a
//! name for them and every retrieval tool this repository has —
//! `shape_search`, `prelude_theorem_inventory`,
//! `kernel_declaration_projection` — is structurally blind to them. A lane that
//! needs `∃`-elimination on a `dvd` hypothesis cannot find the fourteen
//! existing copies, so it writes a fifteenth.
//! `scripts/private-helper-census.py` measured what the four families below
//! cost before this module: 15 copies of `dvd_elim`, 14 of `absurd`, 11 of
//! `dvd_intro`, 10 of `or_cases` — 50 private items, of which 40 were BYTE
//! IDENTICAL after normalization and the other 10 differed only in local
//! binding names and whether `crate::` was spelled out.
//!
//! One copy in one named place does not make them retrievable — a `pub(crate)`
//! helper still declares nothing — but it makes them *findable by reading*, and
//! it is what the shape index would need to index if it ever indexes helpers.
//!
//! WHY THEY ARE GENERIC OVER [`NatOps`] RATHER THAN WRITTEN PER CARRIER. Two of
//! the `dvd_elim` copies live in `int_prelude` over `&mut IntDev`, and
//! the census found their normalized bodies IDENTICAL to the `nat_prelude`
//! copies over `&mut NatDev` — the carrier type was the only difference. That
//! is not a coincidence: `IntDev`'s own `Int`-carrier operations are all
//! `i`-prefixed (`imul`, `ieq`, `iadd`, …) and its `impl NatOps` supplies only
//! `kernel` and `nat_state`, so `mul`, `eq`, `dvd` and `dvd_predicate` on an
//! `IntDev` already ARE the `Nat`-carrier trait defaults. Nothing here is
//! shadowed by an inherent method on any implementor, which is the hazard that
//! makes `NatOps::congr` and `IntDev::irefl` carrier-specific and would have
//! turned a cross-carrier call into one opaque `TypeMismatch`.
//!
//! WHY NO `&NatPrelude` PARAMETER. Roughly half the former copies took the
//! prelude as an explicit argument and half read it from the development. They
//! are the same names either way — a development is constructed over the
//! prelude its caller passes — and `NatOps::prelude` is the accessor that
//! exists for this, so the argument is dropped. `kernel_declaration_projection`
//! is byte-identical across the change, which is the check that the two routes
//! really did agree.
//!
//! Every function here only BUILDS a term. None of them declares, so none of
//! them is trusted surface, and the projection must not move when they change.

use super::NatOps;
use crate::BinderInfo;
use crate::expr::ExprId;

/// `False.rec.{0} (fun _ => goal) contradiction : goal`.
///
/// The universe is `0` because `False.rec` here eliminates into `Prop`.
pub(crate) fn absurd<D: NatOps>(d: &mut D, goal: ExprId, contradiction: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = {
        let name = d.prelude().logic.false_;
        d.kernel().const_(name, vec![])
    };
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = {
        let name = d.prelude().logic.false_rec;
        d.kernel().const_(name, vec![zero])
    };
    d.apply(rec, &[motive, contradiction])
}

/// `Or.rec` with a NON-DEPENDENT motive: from `proof : Or left_ty right_ty` and
/// the two minor premises, a proof of `goal`.
///
/// `Or.rec` carries no universe argument — `Or` is a `Prop` with two
/// constructors, so it eliminates only into `Prop`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn or_cases<D: NatOps>(
    d: &mut D,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_minor: ExprId,
    right_minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_name = d.prelude().logic.or;
    let split_ty = d.const_app(or_name, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, split_ty, goal, BinderInfo::Default);
    let rec = {
        let name = d.prelude().logic.or_rec;
        d.kernel().const_(name, vec![])
    };
    d.apply(
        rec,
        &[left_ty, right_ty, motive, left_minor, right_minor, proof],
    )
}

/// A proof of `dvd a n` from a witness `q` and `eq_proof : Eq n (mul a q)`.
///
/// `dvd a n` unfolds to `Exists Nat (fun q => Eq n (mul a q))`, so this is
/// `Exists.intro` at the `Nat` universe.
pub(crate) fn dvd_intro<D: NatOps>(
    d: &mut D,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro = {
        let name = d.prelude().logic.exists_intro;
        d.kernel().const_(name, vec![one])
    };
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}

/// Eliminate `dvd_hyp : dvd divisor dividend`, continuing with the witness `q`
/// and `eq_proof : Eq dividend (mul divisor q)` to build a proof of `goal`.
///
/// `goal` must not mention `q` — the motive built here is non-dependent, which
/// is what lets `Exists.rec` (a `Prop` recursor) apply at all.
pub(crate) fn dvd_elim<D: NatOps>(
    d: &mut D,
    divisor: ExprId,
    dividend: ExprId,
    goal: ExprId,
    dvd_hyp: ExprId,
    continuation: &dyn Fn(&mut D, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let predicate = d.dvd_predicate(divisor, dividend);
    let dvd_ty = d.dvd(divisor, dividend);
    let motive = d.kernel().lam(anon, dvd_ty, goal, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let divisor_q = d.mul(divisor, q);
        let eq_ty = d.eq(dividend, divisor_q);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, q, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let rec = {
        let name = d.prelude().logic.exists_rec;
        d.kernel().const_(name, vec![one])
    };
    d.apply(rec, &[nat, predicate, motive, minor, dvd_hyp])
}
