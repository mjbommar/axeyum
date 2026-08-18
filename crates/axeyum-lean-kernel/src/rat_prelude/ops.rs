//! The proof-construction layer for the rational development.
//!
//! `Rat` is built over the *already constructed* `ℤ`, so the development runs
//! on [`IntDev`] — the same struct the integer scripts use — rather than on a
//! development of its own. The `Rat`-specific builders below are free functions
//! taking a `Copy` [`RatPrelude`] instead of methods, because `IntDev` carries
//! the `Int` names and has nowhere to put a second prelude. That keeps every
//! closure in this module `&mut IntDev<'_>`, so `Int` and `Rat` reasoning
//! interleave without a wrapper type in between.

use super::RatPrelude;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

// --- carrier and field builders -------------------------------------------

/// The expression `Rat`.
pub(super) fn rat_ty(d: &mut IntDev<'_>) -> ExprId {
    let name = d.int().rat;
    d.kernel().const_(name, vec![])
}

/// `Rat.num q`.
pub(super) fn num(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let f = d.int().rat_num;
    d.const_app(f, &[q])
}

/// `Rat.den q`.
pub(super) fn den(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let f = d.int().rat_den;
    d.const_app(f, &[q])
}

/// `Int.ofNat (Rat.den q)` — the denominator, seen as an integer, which is the
/// only shape the cross-multiplication statements ever use it in.
pub(super) fn den_z(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let raw = den(d, q);
    d.of_nat(raw)
}

/// `Rat.den_pos q : 1 ≤ Rat.den q`.
pub(super) fn den_pos(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let f = d.int().rat_den_pos;
    d.const_app(f, &[q])
}

/// `Rat.reduced q : gcd (natAbs (Rat.num q)) (Rat.den q) = 1`.
pub(super) fn reduced(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let f = d.int().rat_reduced;
    d.const_app(f, &[q])
}

/// `Rat.mk n den positive reduced`.
pub(super) fn mk(
    d: &mut IntDev<'_>,
    n: ExprId,
    denominator: ExprId,
    positive: ExprId,
    reduced_proof: ExprId,
) -> ExprId {
    let f = d.int().rat_mk;
    d.const_app(f, &[n, denominator, positive, reduced_proof])
}

/// `Rat.normalize n den positive`.
pub(super) fn normalize(
    d: &mut IntDev<'_>,
    n: ExprId,
    denominator: ExprId,
    positive: ExprId,
) -> ExprId {
    let f = d.int().rat_normalize;
    d.const_app(f, &[n, denominator, positive])
}

/// The type `1 ≤ den` — `Rat`'s positivity field.
pub(super) fn positive_ty(d: &mut IntDev<'_>, denominator: ExprId) -> ExprId {
    let unit = d.num(1);
    NatOps::le(d, unit, denominator)
}

/// The type `gcd (natAbs n) den = 1` — `Rat`'s reducedness field.
pub(super) fn reduced_ty(d: &mut IntDev<'_>, n: ExprId, denominator: ExprId) -> ExprId {
    let nat_abs = d.int().nat_abs;
    let magnitude = d.const_app(nat_abs, &[n]);
    let common = NatOps::gcd(d, magnitude, denominator);
    let unit = d.num(1);
    d.eq(common, unit)
}

/// `1 ≤ succ k`, the positivity every `succ`-shaped denominator carries for
/// free.
pub(super) fn one_le_succ(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let p = d.int().nat;
    let zero = d.zero();
    let base = d.lemma(p.zero_le, &[k]);
    d.lemma(p.le_succ_succ, &[zero, k, base])
}

// --- operations ------------------------------------------------------------

/// `Rat.add a b`.
pub(super) fn radd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().rat_add;
    d.const_app(f, &[a, b])
}

/// `Rat.mul a b`.
pub(super) fn rmul(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().rat_mul;
    d.const_app(f, &[a, b])
}

/// `Rat.neg a`.
pub(super) fn rneg(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().rat_neg;
    d.const_app(f, &[a])
}

/// `Rat.zero`.
pub(super) fn rzero(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `Rat.one`.
pub(super) fn rone(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    d.kernel().const_(p.one, vec![])
}

/// `Rat.le a b`.
pub(super) fn rle(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.le, &[a, b])
}

/// `Rat.lt a b`.
pub(super) fn rlt(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.lt, &[a, b])
}

// --- Eq at Rat -------------------------------------------------------------

/// `Eq.{1} Rat a b` — the carrier is `Sort 1`, like `Int`.
pub(super) fn req(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.eq;
    let eq = d.kernel().const_(name, vec![one]);
    let carrier = rat_ty(d);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} Rat a`.
pub(super) fn rrefl(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.eq_refl;
    let refl = d.kernel().const_(name, vec![one]);
    let carrier = rat_ty(d);
    d.apply(refl, &[carrier, a])
}

/// `Eq.rec.{0,1} Rat p motive refl_case q h`.
pub(super) fn rtransport(
    d: &mut IntDev<'_>,
    p: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let zero = d.kernel().level_zero();
    let one = d.level_one();
    let name = d.int().logic.eq_rec;
    let rec = d.kernel().const_(name, vec![zero, one]);
    let carrier = rat_ty(d);
    d.apply(rec, &[carrier, p, motive, refl_case, q, h])
}

/// `fun (x : Rat) (_ : Eq Rat a x) => body(x)`.
pub(super) fn req_motive(
    d: &mut IntDev<'_>,
    a: ExprId,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let concl = body(d, x);
    let hyp = req(d, a, x);
    let anon = d.anon_name();
    let inner = d.kernel().lam(anon, hyp, concl, BinderInfo::Default);
    let carrier = rat_ty(d);
    d.lam_fv(x_fv, carrier, inner)
}

/// `h : Eq Rat a b ⊢ Eq Rat b a`.
pub(super) fn rsymm(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let motive = req_motive(d, a, &|d, x| req(d, x, a));
    let refl_case = rrefl(d, a);
    rtransport(d, a, motive, refl_case, b, h)
}

/// `h1 : Eq Rat a b`, `h2 : Eq Rat b c ⊢ Eq Rat a c`.
pub(super) fn rtrans(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let motive = req_motive(d, b, &|d, x| req(d, a, x));
    rtransport(d, b, motive, h1, c, h2)
}

/// Chain `Eq Rat start …` through `(next, step)` pairs.
pub(super) fn rchain(
    d: &mut IntDev<'_>,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut current = start;
    let mut proof = rrefl(d, start);
    for &(next, step) in steps {
        proof = rtrans(d, start, current, next, proof, step);
        current = next;
    }
    (current, proof)
}

/// From `h : Eq Rat p q` and a proof of `motive p`, derive `motive q`.
pub(super) fn rat_eq_rewrite(
    d: &mut IntDev<'_>,
    p: ExprId,
    q: ExprId,
    h: ExprId,
    proof: ExprId,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let built = req_motive(d, p, motive);
    rtransport(d, p, built, proof, q, h)
}

/// From `h : Eq Int a b`, derive `Eq Rat (f a) (f b)`.
pub(super) fn int_eq_to_rat(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.ieq_motive(a, &|d, x| {
        let fx = f(d, x);
        req(d, fa, fx)
    });
    let refl_case = rrefl(d, fa);
    d.itransport(a, motive, refl_case, b, h)
}

/// From `h : Eq Nat a b`, derive `Eq Rat (f a) (f b)`.
pub(super) fn nat_eq_to_rat(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        req(d, fa, fx)
    });
    let refl_case = rrefl(d, fa);
    d.transport(a, motive, refl_case, b, h)
}

// --- declaration plumbing --------------------------------------------------

/// Declare `theorem name : ∀ (x_0 … x_{arity-1} : Rat), stmt := fun … => proof`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel **refused**
/// the proof.
pub(super) fn rat_theorem(
    d: &mut IntDev<'_>,
    name: NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (stmt, proof) = build(d, &vars);
    let mut ty = stmt;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, carrier, ty);
        value = d.lam_fv(fv, carrier, value);
    }
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// Eliminate a balanced Bézout certificate `∃ mp mn np nn, g + m·mn + n·nn = m·mp + n·np`
/// into `target`.
///
/// A local copy of the integer-free eliminator `nat_prelude::bezout` keeps
/// private: the four nested predicates are rebuilt from
/// [`NatOps::bezout_equation`], which is public, so the shape cannot drift from
/// the introduction form even though the code is not shared.
pub(super) fn bezout_elim(
    d: &mut IntDev<'_>,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    target: ExprId,
    certificate: ExprId,
    minor: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_name = d.prelude().logic.exists_;
    let rec_name = d.prelude().logic.exists_rec;

    let mp_fv = d.fresh_fvar();
    let mp = d.kernel().fvar(mp_fv);
    let mn_fv = d.fresh_fvar();
    let mn = d.kernel().fvar(mn_fv);
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let nn_fv = d.fresh_fvar();
    let nn = d.kernel().fvar(nn_fv);

    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
    let nn_predicate = d.lam_fv(nn_fv, nat, equation);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let nn_exists = d.apply(exists, &[nat, nn_predicate]);
    let np_predicate = d.lam_fv(np_fv, nat, nn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let np_exists = d.apply(exists, &[nat, np_predicate]);
    let mn_predicate = d.lam_fv(mn_fv, nat, np_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mn_exists = d.apply(exists, &[nat, mn_predicate]);
    let mp_predicate = d.lam_fv(mp_fv, nat, mn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mp_exists = d.apply(exists, &[nat, mp_predicate]);

    let equation_fv = d.fresh_fvar();
    let equation_proof = d.kernel().fvar(equation_fv);
    let core = minor(d, mp, mn, np, nn, equation_proof);
    let nn_minor = {
        let with_equation = d.lam_fv(equation_fv, equation, core);
        d.lam_fv(nn_fv, nat, with_equation)
    };
    let np_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, nn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, nn_predicate, motive, nn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, nn_exists, eliminated);
        d.lam_fv(np_fv, nat, with_witness)
    };
    let mn_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, np_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, np_predicate, motive, np_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, np_exists, eliminated);
        d.lam_fv(mn_fv, nat, with_witness)
    };
    let mp_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, mn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, mn_predicate, motive, mn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, mn_exists, eliminated);
        d.lam_fv(mp_fv, nat, with_witness)
    };
    let motive = d.kernel().lam(anon, mp_exists, target, BinderInfo::Default);
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[nat, mp_predicate, motive, mp_minor, certificate])
}
