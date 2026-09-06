//! `AlgS.Exchange.*` — ADR-1657, roadmap W3-2: what the index calculus of
//! [`super::vector_space_exchange`] buys once it meets `AlgS.Module.linComb`.
//!
//! # The lemma ADR-1627 named as the blocker
//!
//! `linComb R M smul c v n` is `Σ_{i<n} (c i) • (v i)`, folded on the RIGHT
//! (`linComb … (succ j) ≡ M.op (linComb … j) (smul (c j) (v j))`). The
//! Steinitz exchange needs to *pull one term out of that sum by index* —
//! and the index it pulls is not the last one. That is
//! [`ExchangeNames::lin_comb_remove_at_insert_at`]:
//!
//! ```text
//! le i n ->
//!   linComb c v (succ n) ~ M.op (linComb (removeAt i c) (removeAt i v) n)
//!                               (smul (c i) (v i))
//! ```
//!
//! The sum of `succ n` terms is the sum over the family with index `i`
//! deleted, plus the `i`-th term — which is exactly "the linear combination
//! is unchanged up to the swapped term".
//!
//! # Why the `insertAt` form is the one that is proved
//!
//! The two surgeries do not recurse in the same direction as `linComb`.
//! `removeAt`/`insertAt` recurse on the INDEX (peeling `i`), `linComb`
//! recurses on the LENGTH (peeling `n`), and the induction that closes is the
//! one on the length. Running it on the `removeAt` form leaves
//! `removeAt (succ i') c n'` stuck on a variable `n'` at every step. The
//! `insertAt` form ([`ExchangeNames::lin_comb_insert_at`]) does close, because
//! at the top index the boundary split `le_succ_cases` gives exactly the two
//! cases the fold distinguishes:
//!
//! - `le i n'` — the inserted value is strictly inside the prefix, so the top
//!   term is `c n'` shifted (`insertAt_above`) and the induction hypothesis
//!   applies at the SAME families; one `op_swap_last` finishes it.
//! - `i = succ n'` — the inserted value IS the top term (`insertAt_at`), and
//!   the whole prefix is untouched (`insertAt_below`), so
//!   `linComb_ext_below` closes it with no induction hypothesis at all.
//!
//! The `removeAt` form is then a COROLLARY, not a second induction:
//! `insertAt_removeAt` is unconditional and pointwise, so
//! `linComb_ext_below` rewrites `insertAt i (c i) (removeAt i c)` back to `c`
//! and the two forms are one `trans` apart. That asymmetry — surgery
//! recursion versus fold recursion — is the finding ADR-1657 records.
//!
//! # What is declared
//!
//! | name | kind | what it is |
//! |---|---|---|
//! | `AlgS.Exchange.op_swap_last` | theorem | `(a·b)·c ~ (a·c)·b` in any `AlgS.CommGroup` |
//! | `AlgS.Exchange.linComb_ext_below` | theorem | families agreeing below `n` give equivalent sums |
//! | `AlgS.Exchange.linComb_insertAt` | theorem | inserting a term at `i ≤ n` appends it to the sum |
//! | `AlgS.Exchange.linComb_removeAt_insertAt` | theorem | the split: sum = sum-without-`i` + the `i`-th term |
//!
//! `linComb_ext_below` takes `Eq` hypotheses and not `equiv` ones on purpose:
//! every consumer here gets its pointwise agreement from an `AlgS.Index`
//! lemma, and those are `Eq` because the surgeries are ordinary functions.
//! Weakening them to `equiv` inside the lemma would have forced every caller
//! to transport first.

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::name::NameId;

use super::module_setoid::ModuleNames;
use super::structures::{RecordNames, app2, arrow, eq_of, lam_over, pi_over, sel};
use super::structures_setoid::idx;
use super::vector_space_exchange::IndexNames;

// ---------------------------------------------------------------------------
// Free-variable block: 27_xxx, disjoint from `module_setoid` (23_xxx),
// `field_setoid` (24_xxx), `vector_space` (25_xxx) and
// `vector_space_exchange` (26_xxx).
// ---------------------------------------------------------------------------

const R_FV: u64 = 27_000;
const M_FV: u64 = 27_001;
const SM_FV: u64 = 27_002;
const HM_FV: u64 = 27_003;
const G_FV: u64 = 27_004;
const A_FV: u64 = 27_010;
const X_FV: u64 = 27_011;
const EA_FV: u64 = 27_012;
const EB_FV: u64 = 27_013;
const EC_FV: u64 = 27_014;
const C_FV: u64 = 27_020;
const D_FV: u64 = 27_021;
const VEC_FV: u64 = 27_022;
const WEC_FV: u64 = 27_023;
const N_FV: u64 = 27_030;
const I_FV: u64 = 27_031;
const T_FV: u64 = 27_033;
const IH_FV: u64 = 27_034;
const H1_FV: u64 = 27_040;
const H2_FV: u64 = 27_041;
const H3_FV: u64 = 27_042;
const SCRATCH_FV: u64 = 27_050;
const TRANSPORT_FV: u64 = 27_051;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

// ---------------------------------------------------------------------------
// `AlgS.Exchange.op_swap_last`.
// ---------------------------------------------------------------------------

/// `AlgS.Exchange.op_swap_last : forall (G : AlgS.CommGroup) (a b c :
/// G.carrier), G.equiv (G.op (G.op a b) c) (G.op (G.op a c) b)`.
///
/// Assoc, one `opCongr` over `comm`, assoc back. Stated over `AlgS.CommGroup`
/// and not inside the module layer so it is reusable off the module shelf,
/// the way `AlgS.idem_eq_e` is.
fn declare_op_swap_last(
    k: &mut Kernel,
    cg: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use idx::comm_group as g;
    let group_ty = k.const_(cg.ind, vec![]);
    let gv = k.fvar(G_FV);
    let carrier = sel(k, cg, g::CARRIER, gv);
    let equiv = sel(k, cg, g::EQUIV, gv);
    let refl = sel(k, cg, g::EQUIV_REFL, gv);
    let symm = sel(k, cg, g::EQUIV_SYMM, gv);
    let trans = sel(k, cg, g::EQUIV_TRANS, gv);
    let op = sel(k, cg, g::OP, gv);
    let op_congr = sel(k, cg, g::OP_CONGR, gv);
    let assoc = sel(k, cg, g::ASSOC, gv);
    let comm = sel(k, cg, g::COMM, gv);

    let a = k.fvar(EA_FV);
    let b = k.fvar(EB_FV);
    let c = k.fvar(EC_FV);

    let ab = app2(k, op, a, b);
    let ab_c = app2(k, op, ab, c);
    let bc = app2(k, op, b, c);
    let a_bc = app2(k, op, a, bc);
    let cb = app2(k, op, c, b);
    let a_cb = app2(k, op, a, cb);
    let ac = app2(k, op, a, c);
    let ac_b = app2(k, op, ac, b);

    let s1 = t_app(k, assoc, &[a, b, c]); // (a·b)·c ~ a·(b·c)
    let s2 = {
        let ra = k.app(refl, a);
        let cbc = t_app(k, comm, &[b, c]); // b·c ~ c·b
        t_app(k, op_congr, &[a, a, bc, cb, ra, cbc])
    }; // a·(b·c) ~ a·(c·b)
    let s3 = {
        let asc = t_app(k, assoc, &[a, c, b]); // (a·c)·b ~ a·(c·b)
        t_app(k, symm, &[ac_b, a_cb, asc])
    }; // a·(c·b) ~ (a·c)·b

    let t1 = t_app(k, trans, &[ab_c, a_bc, a_cb, s1, s2]);
    let proof = t_app(k, trans, &[ab_c, a_cb, ac_b, t1, s3]);

    let value = lam_over(k, EC_FV, carrier, proof);
    let value = lam_over(k, EB_FV, carrier, value);
    let value = lam_over(k, EA_FV, carrier, value);
    let value = lam_over(k, G_FV, group_ty, value);

    let concl = app2(k, equiv, ab_c, ac_b);
    let ty = pi_over(k, EC_FV, carrier, concl);
    let ty = pi_over(k, EB_FV, carrier, ty);
    let ty = pi_over(k, EA_FV, carrier, ty);
    let ty = pi_over(k, G_FV, group_ty, ty);

    let name = k.name_str(ns, "op_swap_last");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// The scalar-ring / vector-group selector bundle, plus `linComb` application.
// ---------------------------------------------------------------------------

struct ECtx {
    r: ExprId,
    ring_ty: ExprId,
    rc: ExprId,
    req: ExprId,
    rrefl: ExprId,
    m: ExprId,
    group_ty: ExprId,
    mc: ExprId,
    meq: ExprId,
    mrefl: ExprId,
    msymm: ExprId,
    mtrans: ExprId,
    mop: ExprId,
    mop_congr: ExprId,
    smul: ExprId,
    smul_ty: ExprId,
    coeff_ty: ExprId,
    vec_ty: ExprId,
    nat: ExprId,
    nat_succ: ExprId,
}

fn ectx(k: &mut Kernel, lg: &LogicPrelude, cr: &RecordNames, cg: &RecordNames) -> ECtx {
    use idx::comm_group as g;
    use idx::comm_ring as r;
    let ring_ty = k.const_(cr.ind, vec![]);
    let group_ty = k.const_(cg.ind, vec![]);
    let rv = k.fvar(R_FV);
    let mv = k.fvar(M_FV);
    let rc = sel(k, cr, r::CARRIER, rv);
    let mc = sel(k, cg, g::CARRIER, mv);
    let smul_ty = {
        let inner = arrow(k, mc, mc);
        arrow(k, rc, inner)
    };
    let nat = k.const_(lg.nat, vec![]);
    let coeff_ty = arrow(k, nat, rc);
    let vec_ty = arrow(k, nat, mc);
    ECtx {
        r: rv,
        ring_ty,
        rc,
        req: sel(k, cr, r::EQUIV, rv),
        rrefl: sel(k, cr, r::EQUIV_REFL, rv),
        m: mv,
        group_ty,
        mc,
        meq: sel(k, cg, g::EQUIV, mv),
        mrefl: sel(k, cg, g::EQUIV_REFL, mv),
        msymm: sel(k, cg, g::EQUIV_SYMM, mv),
        mtrans: sel(k, cg, g::EQUIV_TRANS, mv),
        mop: sel(k, cg, g::OP, mv),
        mop_congr: sel(k, cg, g::OP_CONGR, mv),
        smul: k.fvar(SM_FV),
        smul_ty,
        coeff_ty,
        vec_ty,
        nat,
        nat_succ: k.const_(lg.nat_succ, vec![]),
    }
}

impl ECtx {
    fn meqv(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.meq, a, b)
    }
    fn act(&self, k: &mut Kernel, a: ExprId, v: ExprId) -> ExprId {
        app2(k, self.smul, a, v)
    }
    fn plus(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.mop, a, b)
    }
    fn succ(&self, k: &mut Kernel, x: ExprId) -> ExprId {
        k.app(self.nat_succ, x)
    }
    fn mtr(
        &self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        t_app(k, self.mtrans, &[a, b, c, h1, h2])
    }
    fn msy(&self, k: &mut Kernel, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        t_app(k, self.msymm, &[a, b, h])
    }
    fn lin_comb(
        &self,
        k: &mut Kernel,
        lin_comb: NameId,
        coeff: ExprId,
        vecs: ExprId,
        n: ExprId,
    ) -> ExprId {
        let t = k.const_(lin_comb, vec![]);
        t_app(k, t, &[self.r, self.m, self.smul, coeff, vecs, n])
    }
    fn close_pi(&self, k: &mut Kernel, body: ExprId) -> ExprId {
        let t = pi_over(k, SM_FV, self.smul_ty, body);
        let t = pi_over(k, M_FV, self.group_ty, t);
        pi_over(k, R_FV, self.ring_ty, t)
    }
    fn close_lam(&self, k: &mut Kernel, body: ExprId) -> ExprId {
        let t = lam_over(k, SM_FV, self.smul_ty, body);
        let t = lam_over(k, M_FV, self.group_ty, t);
        lam_over(k, R_FV, self.ring_ty, t)
    }
}

/// `equiv a b` from `Eq carrier a b`, by `Eq.rec` transport of
/// `equivRefl a` along the equation. The `AlgS.Index` lemmas all conclude
/// `Eq` — the surgeries are ordinary functions — while every congruence on
/// this shelf consumes `equiv`, so this bridge is used in both directions of
/// every proof below.
#[allow(clippy::too_many_arguments)]
fn equiv_of_eq(
    k: &mut Kernel,
    lg: &LogicPrelude,
    carrier: ExprId,
    equiv: ExprId,
    equiv_refl: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let motive = {
        let z = k.fvar(TRANSPORT_FV);
        let concl = app2(k, equiv, a, z);
        let hyp = eq_of(k, lg, l1, carrier, a, z);
        let anon = k.anon();
        let inner = k.lam(anon, hyp, concl, crate::BinderInfo::Default);
        lam_over(k, TRANSPORT_FV, carrier, inner)
    };
    let base = k.app(equiv_refl, a);
    let rec = k.const_(lg.eq_rec, vec![l0, l1]);
    t_app(k, rec, &[carrier, a, motive, base, b, h])
}

// ---------------------------------------------------------------------------
// `AlgS.Exchange.linComb_ext_below`.
// ---------------------------------------------------------------------------

/// `AlgS.Exchange.linComb_ext_below : forall R M smul, IsModule R M smul ->
/// forall (c d : Nat -> R.carrier) (v w : Nat -> M.carrier) (n : Nat),
/// (forall t, AlgS.Index.le (Nat.succ t) n -> Eq R.carrier (c t) (d t)) ->
/// (forall t, AlgS.Index.le (Nat.succ t) n -> Eq M.carrier (v t) (w t)) ->
/// M.equiv (linComb R M smul c v n) (linComb R M smul d w n)`.
///
/// A sum only sees the indices it folds over. `Nat.rec` on `n`; the successor
/// step is one `opCongr` whose left argument is the induction hypothesis at
/// the weakened bound (`le_succ_right`) and whose right argument is
/// `smulCongr` at the top index (`le_refl`).
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_lin_comb_ext_below(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    mn: &ModuleNames,
    ix: &IndexNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let e = ectx(k, lg, cr, cg);
    let nat = e.nat;

    let hm_ty = {
        let t = k.const_(mn.is_module, vec![]);
        t_app(k, t, &[e.r, e.m, e.smul])
    };
    let hm = k.fvar(HM_FV);
    let cf = k.fvar(C_FV);
    let df = k.fvar(D_FV);
    let vf = k.fvar(VEC_FV);
    let wf = k.fvar(WEC_FV);

    // `forall t, le (succ t) n -> Eq <carrier> (f t) (g t)`.
    let agree = |k: &mut Kernel, carrier: ExprId, f: ExprId, g: ExprId, n: ExprId| {
        let t = k.fvar(T_FV);
        let st = e.succ(k, t);
        let bound = {
            let c = k.const_(ix.le, vec![]);
            t_app(k, c, &[st, n])
        };
        let ft = k.app(f, t);
        let gt = k.app(g, t);
        let concl = eq_of(k, lg, l1, carrier, ft, gt);
        let body = arrow(k, bound, concl);
        pi_over(k, T_FV, nat, body)
    };
    let goal_at = |k: &mut Kernel, n: ExprId| {
        let lhs = e.lin_comb(k, mn.lin_comb, cf, vf, n);
        let rhs = e.lin_comb(k, mn.lin_comb, df, wf, n);
        e.meqv(k, lhs, rhs)
    };

    let motive = {
        let n = k.fvar(N_FV);
        let a1 = agree(k, e.rc, cf, df, n);
        let a2 = agree(k, e.mc, vf, wf, n);
        let g = goal_at(k, n);
        let body = arrow(k, a2, g);
        let body = arrow(k, a1, body);
        lam_over(k, N_FV, nat, body)
    };
    let minor_zero = {
        let zero = k.const_(lg.nat_zero, vec![]);
        let a1 = agree(k, e.rc, cf, df, zero);
        let a2 = agree(k, e.mc, vf, wf, zero);
        // Both sums ι-reduce to `M.e`.
        let me = sel(k, cg, idx::comm_group::E, e.m);
        let r = k.app(e.mrefl, me);
        let body = lam_over(k, H2_FV, a2, r);
        lam_over(k, H1_FV, a1, body)
    };
    let minor_succ = {
        let np = k.fvar(N_FV);
        let snp = e.succ(k, np);
        let ih_ty = {
            let a1 = agree(k, e.rc, cf, df, np);
            let a2 = agree(k, e.mc, vf, wf, np);
            let g = goal_at(k, np);
            let body = arrow(k, a2, g);
            arrow(k, a1, body)
        };
        let ih = k.fvar(IH_FV);
        let a1 = agree(k, e.rc, cf, df, snp);
        let a2 = agree(k, e.mc, vf, wf, snp);
        let h1 = k.fvar(H1_FV);
        let h2 = k.fvar(H2_FV);

        // Weaken both hypotheses from `succ n'` to `n'`.
        let weaken = |k: &mut Kernel, h: ExprId| {
            let t = k.fvar(T_FV);
            let st = e.succ(k, t);
            let bound = {
                let c = k.const_(ix.le, vec![]);
                t_app(k, c, &[st, np])
            };
            let hb = k.fvar(H3_FV);
            let lifted = {
                let c = k.const_(ix.le_succ_right, vec![]);
                t_app(k, c, &[st, np, hb])
            };
            let applied = {
                let x = k.app(h, t);
                k.app(x, lifted)
            };
            let body = lam_over(k, H3_FV, bound, applied);
            lam_over(k, T_FV, nat, body)
        };
        let w1 = weaken(k, h1);
        let w2 = weaken(k, h2);
        let ih_at = {
            let x = k.app(ih, w1);
            k.app(x, w2)
        };

        // The top index, from `le_refl n'` (`le (succ n') (succ n')` ι-reduces
        // to `le n' n'`).
        let top = {
            let c = k.const_(ix.le_refl, vec![]);
            k.app(c, np)
        };
        let e1 = {
            let eqn = {
                let x = k.app(h1, np);
                k.app(x, top)
            };
            let cn = k.app(cf, np);
            let dn = k.app(df, np);
            equiv_of_eq(k, lg, e.rc, e.req, e.rrefl, cn, dn, eqn)
        };
        let e2 = {
            let eqn = {
                let x = k.app(h2, np);
                k.app(x, top)
            };
            let vn = k.app(vf, np);
            let wn = k.app(wf, np);
            equiv_of_eq(k, lg, e.mc, e.meq, e.mrefl, vn, wn, eqn)
        };
        let cn = k.app(cf, np);
        let dn = k.app(df, np);
        let vn = k.app(vf, np);
        let wn = k.app(wf, np);
        let sc = {
            let t = k.const_(mn.smul_congr, vec![]);
            let app = t_app(k, t, &[e.r, e.m, e.smul, hm]);
            t_app(k, app, &[cn, dn, vn, wn, e1, e2])
        };
        let lhs_prefix = e.lin_comb(k, mn.lin_comb, cf, vf, np);
        let rhs_prefix = e.lin_comb(k, mn.lin_comb, df, wf, np);
        let lhs_top = e.act(k, cn, vn);
        let rhs_top = e.act(k, dn, wn);
        let body = t_app(
            k,
            e.mop_congr,
            &[lhs_prefix, rhs_prefix, lhs_top, rhs_top, ih_at, sc],
        );
        let body = lam_over(k, H2_FV, a2, body);
        let body = lam_over(k, H1_FV, a1, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, N_FV, nat, body)
    };

    let n = k.fvar(N_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let body = t_app(k, rec, &[motive, minor_zero, minor_succ, n]);
    let value = lam_over(k, N_FV, nat, body);
    let value = lam_over(k, WEC_FV, e.vec_ty, value);
    let value = lam_over(k, VEC_FV, e.vec_ty, value);
    let value = lam_over(k, D_FV, e.coeff_ty, value);
    let value = lam_over(k, C_FV, e.coeff_ty, value);
    let value = lam_over(k, HM_FV, hm_ty, value);
    let value = e.close_lam(k, value);

    let ty = {
        let a1 = agree(k, e.rc, cf, df, n);
        let a2 = agree(k, e.mc, vf, wf, n);
        let g = goal_at(k, n);
        let body = arrow(k, a2, g);
        let body = arrow(k, a1, body);
        let body = pi_over(k, N_FV, nat, body);
        let body = pi_over(k, WEC_FV, e.vec_ty, body);
        let body = pi_over(k, VEC_FV, e.vec_ty, body);
        let body = pi_over(k, D_FV, e.coeff_ty, body);
        let body = pi_over(k, C_FV, e.coeff_ty, body);
        let body = pi_over(k, HM_FV, hm_ty, body);
        e.close_pi(k, body)
    };

    let name = k.name_str(ns, "linComb_ext_below");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// `AlgS.Exchange.linComb_insertAt`.
// ---------------------------------------------------------------------------

/// `AlgS.Exchange.linComb_insertAt : forall R M smul, IsModule R M smul ->
/// forall (a : R.carrier) (x : M.carrier) (c : Nat -> R.carrier)
/// (v : Nat -> M.carrier) (n i : Nat), AlgS.Index.le i n ->
/// M.equiv (linComb R M smul (insertAt R.carrier i a c)
///                           (insertAt M.carrier i x v) (Nat.succ n))
///         (M.op (linComb R M smul c v n) (smul a x))`.
///
/// **Inserting a term anywhere at or below the top appends it to the sum.**
/// `Nat.rec` on the LENGTH with the index universally quantified in the
/// motive; the successor step splits on `le_succ_cases` and the two branches
/// are the two shapes the fold can see.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_lin_comb_insert_at(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    mn: &ModuleNames,
    ix: &IndexNames,
    op_swap_last: NameId,
    lin_comb_ext_below: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let e = ectx(k, lg, cr, cg);
    let nat = e.nat;
    let zero = k.const_(lg.nat_zero, vec![]);

    let hm_ty = {
        let t = k.const_(mn.is_module, vec![]);
        t_app(k, t, &[e.r, e.m, e.smul])
    };
    let hm = k.fvar(HM_FV);
    let a = k.fvar(A_FV);
    let x = k.fvar(X_FV);
    let cf = k.fvar(C_FV);
    let vf = k.fvar(VEC_FV);

    let ins_c = |k: &mut Kernel, i: ExprId| {
        let t = k.const_(ix.insert_at, vec![]);
        t_app(k, t, &[e.rc, i, a, cf])
    };
    let ins_v = |k: &mut Kernel, i: ExprId| {
        let t = k.const_(ix.insert_at, vec![]);
        t_app(k, t, &[e.mc, i, x, vf])
    };
    let le_at = |k: &mut Kernel, p: ExprId, q: ExprId| {
        let t = k.const_(ix.le, vec![]);
        t_app(k, t, &[p, q])
    };
    let goal_at = |k: &mut Kernel, n: ExprId, i: ExprId| {
        let ic = ins_c(k, i);
        let iv = ins_v(k, i);
        let sn = e.succ(k, n);
        let lhs = e.lin_comb(k, mn.lin_comb, ic, iv, sn);
        let prefix = e.lin_comb(k, mn.lin_comb, cf, vf, n);
        let term = e.act(k, a, x);
        let rhs = e.plus(k, prefix, term);
        e.meqv(k, lhs, rhs)
    };

    let motive = {
        let n = k.fvar(N_FV);
        let i = k.fvar(I_FV);
        let hyp = le_at(k, i, n);
        let g = goal_at(k, n, i);
        let body = arrow(k, hyp, g);
        let body = pi_over(k, I_FV, nat, body);
        lam_over(k, N_FV, nat, body)
    };

    // Length zero: the index must be zero, and then both sides ι-reduce to
    // `M.op M.e (smul a x)`.
    let minor_zero = {
        let inner_motive = {
            let i = k.fvar(I_FV);
            let hyp = le_at(k, i, zero);
            let g = goal_at(k, zero, i);
            let body = arrow(k, hyp, g);
            lam_over(k, I_FV, nat, body)
        };
        let inner_zero = {
            let hyp = le_at(k, zero, zero);
            let lhs = {
                let ic = ins_c(k, zero);
                let iv = ins_v(k, zero);
                let one = e.succ(k, zero);
                e.lin_comb(k, mn.lin_comb, ic, iv, one)
            };
            let r = k.app(e.mrefl, lhs);
            lam_over(k, H1_FV, hyp, r)
        };
        let inner_succ = {
            let ip = k.fvar(I_FV);
            let sip = e.succ(k, ip);
            let inner_ih_ty = {
                let hyp = le_at(k, ip, zero);
                let g = goal_at(k, zero, ip);
                arrow(k, hyp, g)
            };
            let hyp = le_at(k, sip, zero);
            let h = k.fvar(H1_FV);
            let g = goal_at(k, zero, sip);
            // `le (succ i') zero ≡ False`.
            let false_ty = k.const_(lg.false_, vec![]);
            let fm = lam_over(k, SCRATCH_FV, false_ty, g);
            let frec = k.const_(lg.false_rec, vec![l0]);
            let body = t_app(k, frec, &[fm, h]);
            let body = lam_over(k, H1_FV, hyp, body);
            let body = lam_over(k, SCRATCH_FV, inner_ih_ty, body);
            lam_over(k, I_FV, nat, body)
        };
        let i = k.fvar(I_FV);
        let rec = k.const_(lg.nat_rec, vec![l0]);
        let body = t_app(k, rec, &[inner_motive, inner_zero, inner_succ, i]);
        lam_over(k, I_FV, nat, body)
    };

    let minor_succ = {
        let np = k.fvar(N_FV);
        let snp = e.succ(k, np);
        let ih_ty = {
            let i = k.fvar(I_FV);
            let hyp = le_at(k, i, np);
            let g = goal_at(k, np, i);
            let body = arrow(k, hyp, g);
            pi_over(k, I_FV, nat, body)
        };
        let ih = k.fvar(IH_FV);
        let i = k.fvar(I_FV);
        let hyp = le_at(k, i, snp);
        let h = k.fvar(H1_FV);
        let goal = goal_at(k, snp, i);

        let cases = {
            let t = k.const_(ix.le_succ_cases, vec![]);
            t_app(k, t, &[i, np, h])
        };
        let case_left_ty = le_at(k, i, np);
        let case_right_ty = {
            let sn = e.succ(k, np);
            eq_of(k, lg, l1, nat, i, sn)
        };

        // Branch 1: the inserted index is strictly inside the prefix.
        let on_left = {
            let hl = k.fvar(H2_FV);
            let ic = ins_c(k, i);
            let iv = ins_v(k, i);
            let prefix_l = e.lin_comb(k, mn.lin_comb, ic, iv, snp);
            let prefix_r = {
                let p = e.lin_comb(k, mn.lin_comb, cf, vf, np);
                let term = e.act(k, a, x);
                e.plus(k, p, term)
            };
            let step1 = {
                let z = k.app(ih, i);
                k.app(z, hl)
            };
            // The top term: `insertAt i a c (succ n') = c n'` since `i <= n'`.
            let ic_top = k.app(ic, snp);
            let iv_top = k.app(iv, snp);
            let cn = k.app(cf, np);
            let vn = k.app(vf, np);
            let e1 = {
                let t = k.const_(ix.insert_at_above, vec![]);
                let eqn = t_app(k, t, &[e.rc, a, i, cf, np, hl]);
                equiv_of_eq(k, lg, e.rc, e.req, e.rrefl, ic_top, cn, eqn)
            };
            let e2 = {
                let t = k.const_(ix.insert_at_above, vec![]);
                let eqn = t_app(k, t, &[e.mc, x, i, vf, np, hl]);
                equiv_of_eq(k, lg, e.mc, e.meq, e.mrefl, iv_top, vn, eqn)
            };
            let sc = {
                let t = k.const_(mn.smul_congr, vec![]);
                let app = t_app(k, t, &[e.r, e.m, e.smul, hm]);
                t_app(k, app, &[ic_top, cn, iv_top, vn, e1, e2])
            };
            let top_l = e.act(k, ic_top, iv_top);
            let top_r = e.act(k, cn, vn);
            let step2 = t_app(
                k,
                e.mop_congr,
                &[prefix_l, prefix_r, top_l, top_r, step1, sc],
            );
            // `(L·A)·B ~ (L·B)·A`, which IS the right-hand side.
            let inner_prefix = e.lin_comb(k, mn.lin_comb, cf, vf, np);
            let term_ax = e.act(k, a, x);
            let step3 = {
                let t = k.const_(op_swap_last, vec![]);
                t_app(k, t, &[e.m, inner_prefix, term_ax, top_r])
            };
            let mid = e.plus(k, prefix_r, top_r);
            let lhs = e.plus(k, prefix_l, top_l);
            let swapped = {
                let inner = e.plus(k, inner_prefix, top_r);
                e.plus(k, inner, term_ax)
            };
            let body = e.mtr(k, lhs, mid, swapped, step2, step3);
            lam_over(k, H2_FV, case_left_ty, body)
        };

        // Branch 2: the inserted index IS the top of the sum.
        let on_right = {
            let hr = k.fvar(H2_FV);
            // Prove the goal at `i := succ n'`, then transport backwards.
            let at_top = {
                let ic = ins_c(k, snp);
                let iv = ins_v(k, snp);
                let prefix_l = e.lin_comb(k, mn.lin_comb, ic, iv, snp);
                let prefix_r = e.lin_comb(k, mn.lin_comb, cf, vf, snp);
                // The prefix is untouched: every `t` below `succ n'` is
                // strictly below the insertion point.
                let below_c = {
                    let t = k.fvar(T_FV);
                    let st = e.succ(k, t);
                    let bound = le_at(k, st, snp);
                    let hb = k.fvar(H3_FV);
                    let cst = k.const_(ix.insert_at_below, vec![]);
                    let eqn = t_app(k, cst, &[e.rc, a, snp, cf, t, hb]);
                    let body = lam_over(k, H3_FV, bound, eqn);
                    lam_over(k, T_FV, nat, body)
                };
                let below_v = {
                    let t = k.fvar(T_FV);
                    let st = e.succ(k, t);
                    let bound = le_at(k, st, snp);
                    let hb = k.fvar(H3_FV);
                    let cst = k.const_(ix.insert_at_below, vec![]);
                    let eqn = t_app(k, cst, &[e.mc, x, snp, vf, t, hb]);
                    let body = lam_over(k, H3_FV, bound, eqn);
                    lam_over(k, T_FV, nat, body)
                };
                let ext = {
                    let t = k.const_(lin_comb_ext_below, vec![]);
                    let app = t_app(k, t, &[e.r, e.m, e.smul, hm]);
                    t_app(k, app, &[ic, cf, iv, vf, snp, below_c, below_v])
                };
                // The top term IS the inserted one.
                let ic_top = k.app(ic, snp);
                let iv_top = k.app(iv, snp);
                let e1 = {
                    let t = k.const_(ix.insert_at_at, vec![]);
                    let eqn = t_app(k, t, &[e.rc, a, snp, cf]);
                    equiv_of_eq(k, lg, e.rc, e.req, e.rrefl, ic_top, a, eqn)
                };
                let e2 = {
                    let t = k.const_(ix.insert_at_at, vec![]);
                    let eqn = t_app(k, t, &[e.mc, x, snp, vf]);
                    equiv_of_eq(k, lg, e.mc, e.meq, e.mrefl, iv_top, x, eqn)
                };
                let sc = {
                    let t = k.const_(mn.smul_congr, vec![]);
                    let app = t_app(k, t, &[e.r, e.m, e.smul, hm]);
                    t_app(k, app, &[ic_top, a, iv_top, x, e1, e2])
                };
                let top_l = e.act(k, ic_top, iv_top);
                let top_r = e.act(k, a, x);
                t_app(k, e.mop_congr, &[prefix_l, prefix_r, top_l, top_r, ext, sc])
            };
            // `Eq.rec` from `succ n'` to `i` along `Eq.symm hr`.
            let motive_t = {
                let z = k.fvar(TRANSPORT_FV);
                let g = goal_at(k, snp, z);
                let hyp = eq_of(k, lg, l1, nat, snp, z);
                let anon = k.anon();
                let inner = k.lam(anon, hyp, g, crate::BinderInfo::Default);
                lam_over(k, TRANSPORT_FV, nat, inner)
            };
            let sym = {
                let t = k.const_(lg.eq_symm, vec![l1]);
                t_app(k, t, &[nat, i, snp, hr])
            };
            let rec = k.const_(lg.eq_rec, vec![l0, l1]);
            let body = t_app(k, rec, &[nat, snp, motive_t, at_top, i, sym]);
            lam_over(k, H2_FV, case_right_ty, body)
        };

        let elim = k.const_(lg.or_elim, vec![]);
        let body = t_app(
            k,
            elim,
            &[case_left_ty, case_right_ty, goal, cases, on_left, on_right],
        );
        let body = lam_over(k, H1_FV, hyp, body);
        let body = lam_over(k, I_FV, nat, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, N_FV, nat, body)
    };

    let n = k.fvar(N_FV);
    let i = k.fvar(I_FV);
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let outer = t_app(k, rec, &[motive, minor_zero, minor_succ, n]);
    let body = k.app(outer, i);
    let value = lam_over(k, I_FV, nat, body);
    let value = lam_over(k, N_FV, nat, value);
    let value = lam_over(k, VEC_FV, e.vec_ty, value);
    let value = lam_over(k, C_FV, e.coeff_ty, value);
    let value = lam_over(k, X_FV, e.mc, value);
    let value = lam_over(k, A_FV, e.rc, value);
    let value = lam_over(k, HM_FV, hm_ty, value);
    let value = e.close_lam(k, value);

    let ty = {
        let hyp = le_at(k, i, n);
        let g = goal_at(k, n, i);
        let body = arrow(k, hyp, g);
        let body = pi_over(k, I_FV, nat, body);
        let body = pi_over(k, N_FV, nat, body);
        let body = pi_over(k, VEC_FV, e.vec_ty, body);
        let body = pi_over(k, C_FV, e.coeff_ty, body);
        let body = pi_over(k, X_FV, e.mc, body);
        let body = pi_over(k, A_FV, e.rc, body);
        let body = pi_over(k, HM_FV, hm_ty, body);
        e.close_pi(k, body)
    };

    let name = k.name_str(ns, "linComb_insertAt");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// `AlgS.Exchange.linComb_removeAt_insertAt` — the split.
// ---------------------------------------------------------------------------

/// `AlgS.Exchange.linComb_removeAt_insertAt : forall R M smul,
/// IsModule R M smul -> forall (c : Nat -> R.carrier) (v : Nat -> M.carrier)
/// (n i : Nat), AlgS.Index.le i n ->
/// M.equiv (linComb R M smul c v (Nat.succ n))
///         (M.op (linComb R M smul (removeAt R.carrier i c)
///                                 (removeAt M.carrier i v) n)
///               (smul (c i) (v i)))`.
///
/// **The lemma ADR-1627 named as the blocker.** A sum of `succ n` terms is
/// the sum over the family with index `i` deleted, plus the `i`-th term. No
/// second induction: `insertAt_removeAt` is unconditional and pointwise, so
/// `linComb_ext_below` rewrites `insertAt i (c i) (removeAt i c)` back to `c`
/// and one `trans` reaches [`declare_lin_comb_insert_at`].
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_lin_comb_remove_at_insert_at(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    mn: &ModuleNames,
    ix: &IndexNames,
    lin_comb_ext_below: NameId,
    lin_comb_insert_at: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let e = ectx(k, lg, cr, cg);
    let nat = e.nat;

    let hm_ty = {
        let t = k.const_(mn.is_module, vec![]);
        t_app(k, t, &[e.r, e.m, e.smul])
    };
    let hm = k.fvar(HM_FV);
    let cf = k.fvar(C_FV);
    let vf = k.fvar(VEC_FV);
    let n = k.fvar(N_FV);
    let i = k.fvar(I_FV);
    let hyp = {
        let t = k.const_(ix.le, vec![]);
        t_app(k, t, &[i, n])
    };
    let h = k.fvar(H1_FV);

    let ci = k.app(cf, i);
    let vi = k.app(vf, i);
    let rem_c = {
        let t = k.const_(ix.remove_at, vec![]);
        t_app(k, t, &[e.rc, i, cf])
    };
    let rem_v = {
        let t = k.const_(ix.remove_at, vec![]);
        t_app(k, t, &[e.mc, i, vf])
    };
    let ins_c = {
        let t = k.const_(ix.insert_at, vec![]);
        t_app(k, t, &[e.rc, i, ci, rem_c])
    };
    let ins_v = {
        let t = k.const_(ix.insert_at, vec![]);
        t_app(k, t, &[e.mc, i, vi, rem_v])
    };

    let sn = e.succ(k, n);
    let lhs = e.lin_comb(k, mn.lin_comb, cf, vf, sn);
    let mid = e.lin_comb(k, mn.lin_comb, ins_c, ins_v, sn);
    let rhs = {
        let p = e.lin_comb(k, mn.lin_comb, rem_c, rem_v, n);
        let term = e.act(k, ci, vi);
        e.plus(k, p, term)
    };

    // `linComb (insertAt i (c i) (removeAt i c)) … (succ n) ~ linComb c v
    // (succ n)`: the two families agree at EVERY index, so the bound is not
    // used at all.
    let ext = {
        let agree = |k: &mut Kernel, carrier: ExprId, f: ExprId| {
            let t = k.fvar(T_FV);
            let st = e.succ(k, t);
            let bound = {
                let c = k.const_(ix.le, vec![]);
                t_app(k, c, &[st, sn])
            };
            let cst = k.const_(ix.insert_at_remove_at, vec![]);
            let eqn = t_app(k, cst, &[carrier, i, f, t]);
            let body = lam_over(k, H3_FV, bound, eqn);
            lam_over(k, T_FV, nat, body)
        };
        let ac = agree(k, e.rc, cf);
        let av = agree(k, e.mc, vf);
        let t = k.const_(lin_comb_ext_below, vec![]);
        let app = t_app(k, t, &[e.r, e.m, e.smul, hm]);
        t_app(k, app, &[ins_c, cf, ins_v, vf, sn, ac, av])
    };
    // `ext : equiv mid lhs` — `linComb_ext_below` rewrites the SURGERED
    // family into the original, so the symmetry is taken at `(mid, lhs)` and
    // not at `(lhs, mid)`.
    let back = e.msy(k, mid, lhs, ext);
    let step = {
        let t = k.const_(lin_comb_insert_at, vec![]);
        let app = t_app(k, t, &[e.r, e.m, e.smul, hm]);
        t_app(k, app, &[ci, vi, rem_c, rem_v, n, i, h])
    };
    let proof = e.mtr(k, lhs, mid, rhs, back, step);

    let value = lam_over(k, H1_FV, hyp, proof);
    let value = lam_over(k, I_FV, nat, value);
    let value = lam_over(k, N_FV, nat, value);
    let value = lam_over(k, VEC_FV, e.vec_ty, value);
    let value = lam_over(k, C_FV, e.coeff_ty, value);
    let value = lam_over(k, HM_FV, hm_ty, value);
    let value = e.close_lam(k, value);

    let concl = e.meqv(k, lhs, rhs);
    let ty = arrow(k, hyp, concl);
    let ty = pi_over(k, I_FV, nat, ty);
    let ty = pi_over(k, N_FV, nat, ty);
    let ty = pi_over(k, VEC_FV, e.vec_ty, ty);
    let ty = pi_over(k, C_FV, e.coeff_ty, ty);
    let ty = pi_over(k, HM_FV, hm_ty, ty);
    let ty = e.close_pi(k, ty);

    let name = k.name_str(ns, "linComb_removeAt_insertAt");
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
pub struct ExchangeNames {
    pub op_swap_last: NameId,
    pub lin_comb_ext_below: NameId,
    pub lin_comb_insert_at: NameId,
    pub lin_comb_remove_at_insert_at: NameId,
}

/// `#[cfg(test)]` for the same reason `ModuleNames::all` is: these names are
/// deliberately not threaded into `NatPrelude`.
#[cfg(test)]
impl ExchangeNames {
    #[must_use]
    pub fn owned_names(&self) -> [NameId; 4] {
        [
            self.op_swap_last,
            self.lin_comb_ext_below,
            self.lin_comb_insert_at,
            self.lin_comb_remove_at_insert_at,
        ]
    }
}

/// Declare `AlgS.Exchange.*`. Needs `AlgS.CommRing`/`AlgS.CommGroup`,
/// `AlgS.Module.*`'s own names, and `AlgS.Index.*`.
pub(crate) fn declare_exchange(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    mn: &ModuleNames,
    ix: &IndexNames,
    algs: NameId,
) -> Result<ExchangeNames, KernelError> {
    let ns = k.name_str(algs, "Exchange");
    let op_swap_last = declare_op_swap_last(k, cg, ns)?;
    let lin_comb_ext_below = declare_lin_comb_ext_below(k, lg, cr, cg, mn, ix, ns)?;
    let lin_comb_insert_at =
        declare_lin_comb_insert_at(k, lg, cr, cg, mn, ix, op_swap_last, lin_comb_ext_below, ns)?;
    let lin_comb_remove_at_insert_at = declare_lin_comb_remove_at_insert_at(
        k,
        lg,
        cr,
        cg,
        mn,
        ix,
        lin_comb_ext_below,
        lin_comb_insert_at,
        ns,
    )?;
    Ok(ExchangeNames {
        op_swap_last,
        lin_comb_ext_below,
        lin_comb_insert_at,
        lin_comb_remove_at_insert_at,
    })
}

#[cfg(test)]
#[path = "vector_space_steinitz_tests.rs"]
mod vector_space_steinitz_tests;
