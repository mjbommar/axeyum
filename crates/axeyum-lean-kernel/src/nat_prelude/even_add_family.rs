//! `Nat.even_add`/`Nat.even_add'` (lane `parity-finish`, 2026-08-30):
//! `∀ m n, Iff (Even (add m n)) (Iff (Even m) (Even n))` and its `Odd` twin
//! `Iff (Even (add m n)) (Iff (Odd m) (Odd n))` --
//! `F:ml430-nat-even-add-31386639`/`F:ml430-nat-even-add-39e3bc07`.
//!
//! ## Why witnesses, not `mod`
//!
//! `int_prelude/parity.rs`'s `even_add`/`even_add'` case-split on `m % 2`/
//! `n % 2` via `emod_two_eq_zero_or_one` and combine via a `ModEq`-additivity
//! lemma. This prelude's `Nat.Even`/`Nat.Odd` are EXISTENTIAL witnesses
//! (`Even n := Exists k, n = add k k`), so this module case-splits on
//! `even_or_odd_exists` instead and reasons about the witnesses directly:
//! `Nat.add_add_add_comm` (`(a+b)+(c+d)=(a+c)+(b+d)`) plus `Nat.succ_add`
//! (and the DEFINITIONAL `add x (succ y) ≡ succ (add x y)`, since `add`
//! recurses on its right argument) are enough to relate `add m n`'s witness
//! to `m`'s and `n`'s, with no new arithmetic lemma needed.
//!
//! ## Shared structure
//!
//! [`sum_shape`] computes, for witnesses `k`/`j` of `m`/`n` (chosen
//! even-or-odd per `m_odd`/`n_odd`), `add m n`'s own witness `w` and parity,
//! plus the proof relating them -- four cases by the obvious rollover: `EE`
//! closes by `add_add_add_comm` alone; `EO`/`OE` need one `succ_add` (the
//! other side's successor is peeled by `add`'s recursion for free, by
//! defeq); `OO` needs `succ_add` twice plus one more step re-associating
//! `succ (succ (w+w))` into `(succ w)+(succ w)`.
//!
//! The rest ([`TruthFact`], [`iff_fact`], [`mk_iff_both_true`],
//! [`mk_iff_both_false`], [`refute_iff_from_mp`]/[`refute_iff_from_mpr`],
//! [`expect_holds`]) is a direct structural port of
//! `int_prelude/parity.rs`'s combine machinery: the four-way "how do two
//! decided facts combine into an `Iff`" logic does not depend on how the
//! facts were decided, only on whether each `Holds` or is `Refuted`.
//! [`even_add_family_stmt_and_proof`] is generic over which predicate
//! (`Even`/`Odd`) supplies the INNER `Iff`, mirroring
//! `int_prelude/parity.rs`'s `inner_fact`/`inner_pred` parameters.
//!
//! `or_elim`/`absurd`/`with_hyps` are private per-file copies of the
//! non-dependent `Or.rec`/`False.rec`/hypothesis-binder wrappers several
//! other files in this prelude each carry independently (see
//! `parity_div.rs`'s module doc for why this is the convention).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use super::parity::even_predicate;
use super::parity::odd_predicate;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// Non-dependent `Or.rec` (private per-file copy).
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `False.rec` into `goal` (private per-file copy).
fn absurd(d: &mut NatDev<'_>, p: &NatPrelude, goal: ExprId, contradiction: ExprId) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// `fun (h_0 : tys[0]) … => body(h_0, …)` -- module-private copy of the
/// hypothesis-binder wrapper several other files keep privately.
fn with_hyps(
    d: &mut NatDev<'_>,
    tys: &[ExprId],
    body: &dyn Fn(&mut NatDev<'_>, &[ExprId]) -> ExprId,
) -> ExprId {
    let fvs: Vec<u64> = (0..tys.len()).map(|_| d.fresh_fvar()).collect();
    let hyps: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let mut term = body(d, &hyps);
    for (index, &fv) in fvs.iter().enumerate().rev() {
        term = d.lam_fv(fv, tys[index], term);
    }
    term
}

/// A proposition this module has decided one way or the other in the
/// current branch: either a proof it `Holds`, or a proof it is `Refuted`
/// (`Not p`).
enum TruthFact {
    Holds(ExprId),
    Refuted(ExprId),
}

/// Whichever proof `fact` carries -- used only where the caller's own case
/// analysis has already established the fact must be `Holds`; a mismatch
/// would be a bug the kernel's own type check at `add_declaration` catches,
/// not this function.
fn expect_holds(fact: &TruthFact) -> ExprId {
    match *fact {
        TruthFact::Holds(x) | TruthFact::Refuted(x) => x,
    }
}

/// `Iff pa pb` from `Not pa` and `Not pb` both held -- both directions fire
/// vacuously through the refuted antecedent.
fn mk_iff_both_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pa: ExprId,
    pb: ExprId,
    not_pa: ExprId,
    not_pb: ExprId,
) -> ExprId {
    let p = *p;
    let mp = with_hyps(d, &[pa], &|d, h| {
        let f = d.apply(not_pa, &[h[0]]);
        absurd(d, &p, pb, f)
    });
    let mpr = with_hyps(d, &[pb], &|d, h| {
        let f = d.apply(not_pb, &[h[0]]);
        absurd(d, &p, pa, f)
    });
    d.const_app(p.logic.iff_intro, &[pa, pb, mp, mpr])
}

/// `Iff pa pb` from `pa` and `pb` both held -- both directions are constant
/// functions.
fn mk_iff_both_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pa: ExprId,
    pb: ExprId,
    pa_proof: ExprId,
    pb_proof: ExprId,
) -> ExprId {
    let p = *p;
    let mp = {
        let h_fv = d.fresh_fvar();
        d.lam_fv(h_fv, pa, pb_proof)
    };
    let mpr = {
        let h_fv = d.fresh_fvar();
        d.lam_fv(h_fv, pb, pa_proof)
    };
    d.const_app(p.logic.iff_intro, &[pa, pb, mp, mpr])
}

/// From `h : Iff pa pb`, `pa_proof : pa`, `not_pb : Not pb`, derive `False`.
fn refute_iff_from_mp(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pa: ExprId,
    pb: ExprId,
    h: ExprId,
    pa_proof: ExprId,
    not_pb: ExprId,
) -> ExprId {
    let p = *p;
    let mp = d.const_app(p.logic.iff_mp, &[pa, pb, h]);
    let pb_proof = d.apply(mp, &[pa_proof]);
    d.apply(not_pb, &[pb_proof])
}

/// From `h : Iff pa pb`, `pb_proof : pb`, `not_pa : Not pa`, derive `False`
/// -- the `mpr` mirror of [`refute_iff_from_mp`].
fn refute_iff_from_mpr(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pa: ExprId,
    pb: ExprId,
    h: ExprId,
    pb_proof: ExprId,
    not_pa: ExprId,
) -> ExprId {
    let p = *p;
    let mpr = d.const_app(p.logic.iff_mpr, &[pa, pb, h]);
    let pa_proof = d.apply(mpr, &[pb_proof]);
    d.apply(not_pa, &[pa_proof])
}

/// `Iff pa pb` as a [`TruthFact`], from `fa`/`fb` -- the four-way combine
/// every branch of [`declare_even_add`]/[`declare_even_add_prime`] bottoms
/// out in: both hold (constant functions), both refuted (vacuous both
/// ways), or exactly one of each (the whole `Iff` is refuted).
fn iff_fact(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pa: ExprId,
    pb: ExprId,
    fa: &TruthFact,
    fb: &TruthFact,
) -> TruthFact {
    let p = *p;
    match (fa, fb) {
        (TruthFact::Holds(a), TruthFact::Holds(b)) => {
            TruthFact::Holds(mk_iff_both_true(d, &p, pa, pb, *a, *b))
        }
        (TruthFact::Refuted(a), TruthFact::Refuted(b)) => {
            TruthFact::Holds(mk_iff_both_false(d, &p, pa, pb, *a, *b))
        }
        (TruthFact::Holds(a), TruthFact::Refuted(b)) => {
            let (a, b) = (*a, *b);
            let iff_ty = d.const_app(p.logic.iff, &[pa, pb]);
            let refute = with_hyps(d, &[iff_ty], &|d, h| {
                refute_iff_from_mp(d, &p, pa, pb, h[0], a, b)
            });
            TruthFact::Refuted(refute)
        }
        (TruthFact::Refuted(a), TruthFact::Holds(b)) => {
            let (a, b) = (*a, *b);
            let iff_ty = d.const_app(p.logic.iff, &[pa, pb]);
            let refute = with_hyps(d, &[iff_ty], &|d, h| {
                refute_iff_from_mpr(d, &p, pa, pb, h[0], b, a)
            });
            TruthFact::Refuted(refute)
        }
    }
}

/// Existentially eliminate `hx : (Even|Odd) x` (per `is_odd`) into its
/// witness `k` and equation `hk : Eq x (add k k)` (`is_odd = false`) or
/// `hk : Eq x (succ (add k k))` (`is_odd = true`), to prove the
/// non-dependent `goal`.
#[allow(clippy::too_many_arguments)]
fn elim_parity(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    is_odd: bool,
    hx_ty: ExprId,
    hx: ExprId,
    goal: ExprId,
    body: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = if is_odd {
        odd_predicate(d, x)
    } else {
        even_predicate(d, x)
    };
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let form = if is_odd { d.succ(kk) } else { kk };
    let hk_ty = d.eq(x, form);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);
    let inner = body(d, k, hk);
    let minor = d.lam_fv(hk_fv, hk_ty, inner);
    let minor = d.lam_fv(k_fv, nat, minor);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, hx_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, hx])
}

/// `add m n`'s own witness/parity, given `m`'s/`n`'s witness equations
/// `m_eq`/`n_eq` (matching `m_odd`/`n_odd`) -- returns `(w, result_odd,
/// proof : Eq (add m n) (if result_odd { succ (add w w) } else { add w w
/// }))`. See the module doc for the four-case rollover.
#[allow(clippy::too_many_arguments)]
fn sum_shape(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    k: ExprId,
    j: ExprId,
    m_odd: bool,
    n_odd: bool,
    m_eq: ExprId,
    n_eq: ExprId,
) -> (ExprId, bool, ExprId) {
    let p = *p;
    let kk = d.add(k, k);
    let jj = d.add(j, j);
    let kj = d.add(k, j);
    let target_ee = d.add(kj, kj);
    let kk_jj = d.add(kk, jj);

    let m_form = if m_odd { d.succ(kk) } else { kk };
    let n_form = if n_odd { d.succ(jj) } else { jj };

    let mn = d.add(m, n);
    let step1_rhs = d.add(m_form, n);
    let step1 = d.congr(m, m_form, m_eq, &|d, x| d.add(x, n));
    let step2_rhs = d.add(m_form, n_form);
    let step2 = d.congr(n, n_form, n_eq, &|d, x| d.add(m_form, x));

    let comm = d.lemma(p.add_add_add_comm, &[k, k, j, j]);

    match (m_odd, n_odd) {
        (false, false) => {
            let (_end, chained) =
                d.chain(mn, &[(step1_rhs, step1), (step2_rhs, step2), (target_ee, comm)]);
            (kj, false, chained)
        }
        (false, true) => {
            // step2_rhs = add(kk, succ jj) ≡ succ(kk_jj), definitionally.
            let succ_kk_jj = d.succ(kk_jj);
            let defeq_step = d.refl(step2_rhs);
            let succ_target = d.succ(target_ee);
            let congr_comm = d.congr(kk_jj, target_ee, comm, &|d, x| d.succ(x));
            let (_end, chained) = d.chain(
                mn,
                &[
                    (step1_rhs, step1),
                    (step2_rhs, step2),
                    (succ_kk_jj, defeq_step),
                    (succ_target, congr_comm),
                ],
            );
            (kj, true, chained)
        }
        (true, false) => {
            // step2_rhs = add(succ kk, jj) = succ(kk_jj), via succ_add.
            let succ_kk_jj = d.succ(kk_jj);
            let sadd = d.lemma(p.succ_add, &[kk, jj]);
            let succ_target = d.succ(target_ee);
            let congr_comm = d.congr(kk_jj, target_ee, comm, &|d, x| d.succ(x));
            let (_end, chained) = d.chain(
                mn,
                &[
                    (step1_rhs, step1),
                    (step2_rhs, step2),
                    (succ_kk_jj, sadd),
                    (succ_target, congr_comm),
                ],
            );
            (kj, true, chained)
        }
        (true, true) => {
            // step2_rhs = add(succ kk, succ jj) ≡ succ(add(succ kk, jj)),
            // definitionally; add(succ kk, jj) = succ(kk_jj) via succ_add.
            let succ_kk = d.succ(kk);
            let mid1 = d.add(succ_kk, jj);
            let succ_mid1 = d.succ(mid1);
            let defeq_step1 = d.refl(step2_rhs);
            let succ_kk_jj = d.succ(kk_jj);
            let sadd = d.lemma(p.succ_add, &[kk, jj]);
            let congr_sadd = d.congr(mid1, succ_kk_jj, sadd, &|d, x| d.succ(x));
            let succ_succ_kk_jj = d.succ(succ_kk_jj);
            let succ_target = d.succ(target_ee);
            let succ_succ_target = d.succ(succ_target);
            let congr_comm = d.congr(kk_jj, target_ee, comm, &|d, x| {
                let sx = d.succ(x);
                d.succ(sx)
            });
            let (_end, chained) = d.chain(
                mn,
                &[
                    (step1_rhs, step1),
                    (step2_rhs, step2),
                    (succ_mid1, defeq_step1),
                    (succ_succ_kk_jj, congr_sadd),
                    (succ_succ_target, congr_comm),
                ],
            );
            // chained : Eq (add m n) (succ (succ target_ee)). Relate that to
            // add(succ kj, succ kj) via succ_add(kj, kj) reversed.
            let succ_kj = d.succ(kj);
            let mid2 = d.add(succ_kj, kj);
            let succ_mid2 = d.succ(mid2);
            let sadd2 = d.lemma(p.succ_add, &[kj, kj]);
            let congr_final = d.congr(mid2, succ_target, sadd2, &|d, x| d.succ(x));
            let symm_final = d.symm(succ_mid2, succ_succ_target, congr_final);
            let target_oo = d.add(succ_kj, succ_kj);
            let (_end2, final_proof) =
                d.chain(mn, &[(succ_succ_target, chained), (target_oo, symm_final)]);
            (succ_kj, false, final_proof)
        }
    }
}

/// One `(m parity, n parity)` leaf's proof of the shared `stmt`, given
/// witnesses `k`/`j`, the OUTER disjunct-level hypotheses `hm`/`hn`
/// (`Even`/`Odd` per `m_odd`/`n_odd`, fed straight to `inner_fact`, never
/// destructured), and the witness equations `hk`/`hj` (fed to
/// [`sum_shape`]).
#[allow(clippy::too_many_arguments)]
fn add_case(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    k: ExprId,
    j: ExprId,
    m_odd: bool,
    n_odd: bool,
    hm: ExprId,
    hn: ExprId,
    hk: ExprId,
    hj: ExprId,
    inner_fact: &dyn Fn(&mut NatDev<'_>, ExprId, bool, ExprId) -> TruthFact,
    inner_pred: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let mn = d.add(m, n);
    let pa = inner_pred(d, m);
    let pb = inner_pred(d, n);
    let inner_ty = d.const_app(p.logic.iff, &[pa, pb]);
    let even_mn_ty = d.lemma(p.even, &[mn]);

    let fm = inner_fact(d, m, m_odd, hm);
    let fnn = inner_fact(d, n, n_odd, hn);

    let (w, result_odd, sum_proof) = sum_shape(d, &p, m, n, k, j, m_odd, n_odd, hk, hj);
    let one = d.level_one();
    let nat = d.nat_ty();
    let fsum = if result_odd {
        let odd_pred_mn = odd_predicate(d, mn);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let odd_proof = d.apply(intro, &[nat, odd_pred_mn, w, sum_proof]);
        let bridge = d.lemma(p.odd_not_even, &[mn]);
        TruthFact::Refuted(d.apply(bridge, &[odd_proof]))
    } else {
        let even_pred_mn = even_predicate(d, mn);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let ev_proof = d.apply(intro, &[nat, even_pred_mn, w, sum_proof]);
        TruthFact::Holds(ev_proof)
    };

    let inner = iff_fact(d, &p, pa, pb, &fm, &fnn);
    let outer = iff_fact(d, &p, even_mn_ty, inner_ty, &fsum, &inner);
    expect_holds(&outer)
}

/// The shared `stmt`/`proof` builder for [`declare_even_add`]/
/// [`declare_even_add_prime`]: `Iff (Even (add m n)) (Iff (P m) (P n))` for
/// `P := Even` or `P := Odd`, via a four-way case split on `m`'s and `n`'s
/// parity (`even_or_odd_exists`).
fn even_add_family_stmt_and_proof(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    inner_fact: &dyn Fn(&mut NatDev<'_>, ExprId, bool, ExprId) -> TruthFact,
    inner_pred: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> (ExprId, ExprId) {
    let p = *p;
    let mn = d.add(m, n);
    let pa0 = inner_pred(d, m);
    let pb0 = inner_pred(d, n);
    let inner_ty0 = d.const_app(p.logic.iff, &[pa0, pb0]);
    let even_mn_ty0 = d.lemma(p.even, &[mn]);
    let stmt = d.const_app(p.logic.iff, &[even_mn_ty0, inner_ty0]);

    let even_m_ty = d.lemma(p.even, &[m]);
    let odd_m_ty = d.lemma(p.odd, &[m]);
    let even_n_ty = d.lemma(p.even, &[n]);
    let odd_n_ty = d.lemma(p.odd, &[n]);
    let or_m = d.lemma(p.even_or_odd_exists, &[m]);
    let or_n = d.lemma(p.even_or_odd_exists, &[n]);

    let m_branch = |d: &mut NatDev<'_>, m_odd: bool, hm_ty: ExprId, hm: ExprId| -> ExprId {
        elim_parity(d, &p, m, m_odd, hm_ty, hm, stmt, &|d, k, hk| {
            let n_even_case = {
                let hn_fv = d.fresh_fvar();
                let hn = d.kernel().fvar(hn_fv);
                let inner = elim_parity(d, &p, n, false, even_n_ty, hn, stmt, &|d, j, hj| {
                    add_case(
                        d, &p, m, n, k, j, m_odd, false, hm, hn, hk, hj, inner_fact, inner_pred,
                    )
                });
                d.lam_fv(hn_fv, even_n_ty, inner)
            };
            let n_odd_case = {
                let hn_fv = d.fresh_fvar();
                let hn = d.kernel().fvar(hn_fv);
                let inner = elim_parity(d, &p, n, true, odd_n_ty, hn, stmt, &|d, j, hj| {
                    add_case(
                        d, &p, m, n, k, j, m_odd, true, hm, hn, hk, hj, inner_fact, inner_pred,
                    )
                });
                d.lam_fv(hn_fv, odd_n_ty, inner)
            };
            or_elim(
                d,
                &p,
                even_n_ty,
                odd_n_ty,
                stmt,
                n_even_case,
                n_odd_case,
                or_n,
            )
        })
    };

    let case_m_even = {
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let body = m_branch(d, false, even_m_ty, hm);
        d.lam_fv(hm_fv, even_m_ty, body)
    };
    let case_m_odd = {
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let body = m_branch(d, true, odd_m_ty, hm);
        d.lam_fv(hm_fv, odd_m_ty, body)
    };

    let proof = or_elim(
        d,
        &p,
        even_m_ty,
        odd_m_ty,
        stmt,
        case_m_even,
        case_m_odd,
        or_m,
    );
    (stmt, proof)
}

fn even_inner_fact(d: &mut NatDev<'_>, x: ExprId, x_odd: bool, hx: ExprId) -> TruthFact {
    let p = d.prelude();
    if x_odd {
        let bridge = d.lemma(p.odd_not_even, &[x]);
        TruthFact::Refuted(d.apply(bridge, &[hx]))
    } else {
        TruthFact::Holds(hx)
    }
}

fn odd_inner_fact(d: &mut NatDev<'_>, x: ExprId, x_odd: bool, hx: ExprId) -> TruthFact {
    let p = d.prelude();
    if x_odd {
        TruthFact::Holds(hx)
    } else {
        let bridge = d.lemma(p.even_not_odd, &[x]);
        TruthFact::Refuted(d.apply(bridge, &[hx]))
    }
}

fn even_inner_pred(d: &mut NatDev<'_>, x: ExprId) -> ExprId {
    let p = d.prelude();
    d.lemma(p.even, &[x])
}

fn odd_inner_pred(d: &mut NatDev<'_>, x: ExprId) -> ExprId {
    let p = d.prelude();
    d.lemma(p.odd, &[x])
}

/// `Nat.even_add : ∀ m n, Iff (Even (add m n)) (Iff (Even m) (Even n))` --
/// `F:ml430-nat-even-add-31386639`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_even_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.even_add, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        even_add_family_stmt_and_proof(d, &p, m, n, &even_inner_fact, &even_inner_pred)
    })?;
    Ok(())
}

/// `Nat.even_add' : ∀ m n, Iff (Even (add m n)) (Iff (Odd m) (Odd n))` --
/// `F:ml430-nat-even-add-39e3bc07`. [`declare_even_add`]'s twin, via
/// [`odd_inner_fact`]/[`odd_inner_pred`] instead of
/// [`even_inner_fact`]/[`even_inner_pred`] for the inner predicate (the
/// outer `Even (add m n)` is unchanged).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_even_add_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.even_add_prime, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        even_add_family_stmt_and_proof(d, &p, m, n, &odd_inner_fact, &odd_inner_pred)
    })?;
    Ok(())
}

/// Declaration order: both facts need only `Nat.Even`/`Nat.Odd`,
/// `even_or_odd_exists`, `even_not_odd`/`odd_not_even` (`parity.rs`) and
/// `add_add_add_comm` (`add_basics.rs`), `succ_add` (core additive
/// theorems) -- all declared well before this cluster's call site in
/// `nat_prelude.rs`.
pub(super) fn declare_even_add_family_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_even_add(d, p)?;
    declare_even_add_prime(d, p)?;
    Ok(())
}
