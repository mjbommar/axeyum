//! `AlgS.VectorSpace.*` — ADR-1627, roadmap W3-2: a vector space is
//! [`super::module_setoid`]'s `IsModule` over an
//! [`super::field_setoid`] `AlgS.Field`, and the two theorems that need the
//! field rather than a ring.
//!
//! # What the field buys, precisely
//!
//! Over a `CommRing` you cannot cancel a scalar: `a•v ~ a•w` does not give
//! `v ~ w`. Over an `AlgS.Field` it does, for any `a` **apart from zero** —
//! [`VectorSpaceNames::smul_left_cancel`] — and, more usefully, you can
//! *solve for a coefficient*: [`VectorSpaceNames::solve_smul`] turns
//! `a•v ~ w` with `a # 0` into `∃ c, v ~ c•w`. That existential conclusion is
//! the atomic step of the Steinitz exchange, and it is the step the whole
//! dimension argument is made of.
//!
//! Both proofs open `AlgS.Field`'s existential inverse with `Exists.rec` into
//! a `Prop` goal. That is the entire reason the field's inverse can be an
//! `Exists` and still be useful, and it is why `CReal` can be a field here at
//! all (see [`super::field_setoid`]'s module doc).
//!
//! # Dimension: what landed and what did not
//!
//! [`VectorSpaceNames::basis_zero_unique`] is **invariance of basis number at
//! zero**: if some family is a basis at length `0` then every basis of the
//! same space has length `0`. It is a genuine instance of "any two bases have
//! the same cardinality", and the proof is exactly the field's non-triviality
//! doing the work — `spans v 0` collapses the space to `M.e`, so
//! `linearIndependent u (succ j)` at the two constant coefficient families
//! `fun _ => one` and `fun _ => zero` forces `equiv one zero`, refuted by
//! `oneApartZero` through `apartCompat`.
//!
//! **The general theorem — `isBasis v n → isBasis u m → n = m` — is NOT
//! here**, and ADR-1627 §6 sizes what it costs rather than promising it. The
//! obstruction is not the field and not `Quot`: it is that the Steinitz
//! exchange rewrites the *indexing* of a coefficient family (replace `v i` by
//! `w`, reindex the rest), and at the `AlgS` build position `Nat.lt`,
//! `Nat.beq` and every `sumRange` reindexing lemma are undeclared —
//! `module_setoid`'s own `coeffAgree` exists only because `Nat.lt` does not.
//!
//! Notice `basis_zero_unique` does **not** take the `IsVectorSpace`
//! hypothesis. That is deliberate and is itself the finding: at length zero
//! the module axioms are not used at all, only the field's non-triviality, so
//! stating it over a module would have been a weaker theorem with a decorative
//! hypothesis.

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

use super::field_setoid::{FieldNames, ix};
use super::module_setoid::ModuleNames;
use super::structures::{RecordNames, app2, arrow, eq_of, lam_over, pi_over, refl_of, sel};
use super::structures_setoid::idx;

// ---------------------------------------------------------------------------
// Free-variable block: 25_xxx, disjoint from `module_setoid` (23_xxx) and
// `field_setoid` (24_xxx).
// ---------------------------------------------------------------------------

const F_FV: u64 = 25_000;
const M_FV: u64 = 25_001;
const SM_FV: u64 = 25_002;
const HM_FV: u64 = 25_003;
const A_FV: u64 = 25_010;
const B_FV: u64 = 25_011;
const V_FV: u64 = 25_012;
const W_FV: u64 = 25_013;
const U_FV: u64 = 25_014;
const N_FV: u64 = 25_020;
const J_FV: u64 = 25_021;
const IH_FV: u64 = 25_022;
const C_FV: u64 = 25_030;
const H1_FV: u64 = 25_040;
const H2_FV: u64 = 25_041;
const H3_FV: u64 = 25_042;
const SCRATCH_FV: u64 = 25_050;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

// ---------------------------------------------------------------------------
// The selector bundle: a field `F`, a commutative group `M`, an action.
// ---------------------------------------------------------------------------

struct VCtx {
    f: ExprId,
    field_ty: ExprId,
    /// `AlgS.Field.toCommRing F`, the scalar ring every `AlgS.Module.*` name
    /// below is applied at.
    ring: ExprId,
    fc: ExprId,
    feq: ExprId,
    frefl: ExprId,
    fsymm: ExprId,
    ftrans: ExprId,
    fzero: ExprId,
    fone: ExprId,
    fmul: ExprId,
    fmul_comm: ExprId,
    fapart: ExprId,
    fapart_compat: ExprId,
    fmul_inv_ex: ExprId,
    m: ExprId,
    group_ty: ExprId,
    mc: ExprId,
    meq: ExprId,
    mrefl: ExprId,
    msymm: ExprId,
    mtrans: ExprId,
    me: ExprId,
    smul: ExprId,
    smul_ty: ExprId,
}

fn vctx(k: &mut Kernel, fr: &RecordNames, cg: &RecordNames, to_comm_ring: NameId) -> VCtx {
    use idx::comm_group as g;
    let field_ty = k.const_(fr.ind, vec![]);
    let group_ty = k.const_(cg.ind, vec![]);
    let f = k.fvar(F_FV);
    let m = k.fvar(M_FV);
    let fc = sel(k, fr, ix::CARRIER, f);
    let mc = sel(k, cg, g::CARRIER, m);
    let smul_ty = {
        let inner = arrow(k, mc, mc);
        arrow(k, fc, inner)
    };
    let ring = {
        let t = k.const_(to_comm_ring, vec![]);
        k.app(t, f)
    };
    VCtx {
        f,
        field_ty,
        ring,
        fc,
        feq: sel(k, fr, ix::EQUIV, f),
        frefl: sel(k, fr, ix::EQUIV_REFL, f),
        fsymm: sel(k, fr, ix::EQUIV_SYMM, f),
        ftrans: sel(k, fr, ix::EQUIV_TRANS, f),
        fzero: sel(k, fr, ix::ZERO, f),
        fone: sel(k, fr, ix::ONE, f),
        fmul: sel(k, fr, ix::MUL, f),
        fmul_comm: sel(k, fr, ix::MUL_COMM, f),
        fapart: sel(k, fr, ix::APART, f),
        fapart_compat: sel(k, fr, ix::APART_COMPAT, f),
        fmul_inv_ex: sel(k, fr, ix::MUL_INV_EX, f),
        m,
        group_ty,
        mc,
        meq: sel(k, cg, g::EQUIV, m),
        mrefl: sel(k, cg, g::EQUIV_REFL, m),
        msymm: sel(k, cg, g::EQUIV_SYMM, m),
        mtrans: sel(k, cg, g::EQUIV_TRANS, m),
        me: sel(k, cg, g::E, m),
        smul: k.fvar(SM_FV),
        smul_ty,
    }
}

impl VCtx {
    fn meqv(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.meq, a, b)
    }
    fn feqv(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.feq, a, b)
    }
    fn act(&self, k: &mut Kernel, a: ExprId, v: ExprId) -> ExprId {
        app2(k, self.smul, a, v)
    }
    fn ftimes(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.fmul, a, b)
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
    fn close_pi(&self, k: &mut Kernel, body: ExprId) -> ExprId {
        let t = pi_over(k, SM_FV, self.smul_ty, body);
        let t = pi_over(k, M_FV, self.group_ty, t);
        pi_over(k, F_FV, self.field_ty, t)
    }
    fn close_lam(&self, k: &mut Kernel, body: ExprId) -> ExprId {
        let t = lam_over(k, SM_FV, self.smul_ty, body);
        let t = lam_over(k, M_FV, self.group_ty, t);
        lam_over(k, F_FV, self.field_ty, t)
    }
}

// ---------------------------------------------------------------------------
// `IsVectorSpace`.
// ---------------------------------------------------------------------------

/// `AlgS.VectorSpace.IsVectorSpace F M smul :=
/// AlgS.Module.IsModule (AlgS.Field.toCommRing F) M smul`.
///
/// A definition and not a new conjunction: a vector space IS a module, and the
/// only thing "vector space" adds is that the scalars form a field, which is
/// carried by `F`'s type. `(AlgS.Field.toCommRing F).carrier` ι-reduces to
/// `F.carrier`, so `smul`'s declared type needs no transport.
fn declare_is_vector_space(
    k: &mut Kernel,
    fr: &RecordNames,
    cg: &RecordNames,
    to_comm_ring: NameId,
    is_module: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = vctx(k, fr, cg, to_comm_ring);
    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let body = {
        let t = k.const_(is_module, vec![]);
        t_app(k, t, &[c.ring, c.m, c.smul])
    };
    let value = c.close_lam(k, body);
    let ty = c.close_pi(k, prop);

    let name = k.name_str(ns, "IsVectorSpace");
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
// The two field-only theorems.
// ---------------------------------------------------------------------------

/// Shared body of the two theorems below: given `b` with `hb : F.equiv (a·b)
/// F.one`, build the chain
/// `v ~ 1•v ~ (b·a)•v ~ b•(a•v)`, and return it together with the two field
/// facts `equiv (b·a) one` and `equiv one (b·a)` the caller still needs.
struct InvChain {
    /// `M.equiv v (smul b (smul a v))`.
    to_b_av: ExprId,
    /// `smul b (smul a v)`, the right-hand side of `to_b_av`.
    b_av: ExprId,
}

fn inv_chain(
    k: &mut Kernel,
    c: &VCtx,
    one_smul: NameId,
    mul_smul: NameId,
    smul_congr: NameId,
    hm: ExprId,
    a: ExprId,
    b: ExprId,
    v: ExprId,
    hb: ExprId,
) -> InvChain {
    let ba = c.ftimes(k, b, a);
    let ab = c.ftimes(k, a, b);
    let comm = t_app(k, c.fmul_comm, &[b, a]); // F.equiv (b·a) (a·b)
    let ba_one = t_app(k, c.ftrans, &[ba, ab, c.fone, comm, hb]); // (b·a) ~ 1
    let one_ba = t_app(k, c.fsymm, &[ba, c.fone, ba_one]); // 1 ~ (b·a)
    // `ba_one` itself is not returned: the two callers both cancel the scalar
    // by rewriting `1` FORWARD into `b·a`, never backward.

    let one_v = c.act(k, c.fone, v);
    let ba_v = c.act(k, ba, v);
    let a_v = c.act(k, a, v);
    let b_av = c.act(k, b, a_v);

    let os = {
        let t = k.const_(one_smul, vec![]);
        let app = t_app(k, t, &[c.ring, c.m, c.smul, hm]);
        k.app(app, v)
    }; // M.equiv (1•v) v
    let os_sym = c.msy(k, one_v, v, os); // v ~ 1•v
    let sc = {
        let t = k.const_(smul_congr, vec![]);
        let app = t_app(k, t, &[c.ring, c.m, c.smul, hm]);
        let rv = k.app(c.mrefl, v);
        t_app(k, app, &[c.fone, ba, v, v, one_ba, rv])
    }; // 1•v ~ (b·a)•v
    let ms = {
        let t = k.const_(mul_smul, vec![]);
        let app = t_app(k, t, &[c.ring, c.m, c.smul, hm]);
        t_app(k, app, &[b, a, v])
    }; // (b·a)•v ~ b•(a•v)

    let t1 = c.mtr(k, one_v, ba_v, b_av, sc, ms);
    let to_b_av = c.mtr(k, v, one_v, b_av, os_sym, t1);
    InvChain { to_b_av, b_av }
}

/// `AlgS.VectorSpace.smul_left_cancel : forall F M smul,
/// IsVectorSpace F M smul -> forall a v w, F.apart a F.zero ->
/// M.equiv (smul a v) (smul a w) -> M.equiv v w`.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_smul_left_cancel(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fr: &RecordNames,
    cg: &RecordNames,
    to_comm_ring: NameId,
    is_vector_space: NameId,
    mn: &ModuleNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = vctx(k, fr, cg, to_comm_ring);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let hm_ty = {
        let t = k.const_(is_vector_space, vec![]);
        t_app(k, t, &[c.f, c.m, c.smul])
    };
    let hm = k.fvar(HM_FV);
    let a = k.fvar(A_FV);
    let v = k.fvar(V_FV);
    let w = k.fvar(W_FV);
    let hap_ty = app2(k, c.fapart, a, c.fzero);
    let a_v = c.act(k, a, v);
    let a_w = c.act(k, a, w);
    let heq_ty = c.meqv(k, a_v, a_w);
    let hap = k.fvar(H1_FV);
    let heq = k.fvar(H2_FV);
    let goal = c.meqv(k, v, w);

    let pred = {
        let bb = k.fvar(B_FV);
        let abb = c.ftimes(k, a, bb);
        let body = c.feqv(k, abb, c.fone);
        lam_over(k, B_FV, c.fc, body)
    };
    let ex = k.const_(lg.exists_, vec![l1]);
    let ex_ty = app2(k, ex, c.fc, pred);
    let motive = lam_over(k, SCRATCH_FV, ex_ty, goal);
    let witness = t_app(k, c.fmul_inv_ex, &[a, hap]);

    let minor = {
        let b = k.fvar(B_FV);
        let ab = c.ftimes(k, a, b);
        let hb_ty = c.feqv(k, ab, c.fone);
        let hb = k.fvar(H3_FV);
        let left = inv_chain(
            k,
            &c,
            mn.one_smul,
            mn.mul_smul,
            mn.smul_congr,
            hm,
            a,
            b,
            v,
            hb,
        );
        let right = inv_chain(
            k,
            &c,
            mn.one_smul,
            mn.mul_smul,
            mn.smul_congr,
            hm,
            a,
            b,
            w,
            hb,
        );
        // `b•(a•v) ~ b•(a•w)` by `smulCongr` on the second argument.
        let mid = {
            let t = k.const_(mn.smul_congr, vec![]);
            let app = t_app(k, t, &[c.ring, c.m, c.smul, hm]);
            let rb = k.app(c.frefl, b);
            t_app(k, app, &[b, b, a_v, a_w, rb, heq])
        };
        // `b•(a•w) ~ w` is `right.to_b_av` symmetrised.
        let back = c.msy(k, w, right.b_av, right.to_b_av);
        let t1 = c.mtr(k, left.b_av, right.b_av, w, mid, back);
        let body = c.mtr(k, v, left.b_av, w, left.to_b_av, t1);
        let inner = lam_over(k, H3_FV, hb_ty, body);
        lam_over(k, B_FV, c.fc, inner)
    };
    let rec = k.const_(lg.exists_rec, vec![l1]);
    let proof = t_app(k, rec, &[c.fc, pred, motive, minor, witness]);

    let value = lam_over(k, H2_FV, heq_ty, proof);
    let value = lam_over(k, H1_FV, hap_ty, value);
    let value = lam_over(k, W_FV, c.mc, value);
    let value = lam_over(k, V_FV, c.mc, value);
    let value = lam_over(k, A_FV, c.fc, value);
    let value = lam_over(k, HM_FV, hm_ty, value);
    let value = c.close_lam(k, value);

    let ty = arrow(k, heq_ty, goal);
    let ty = arrow(k, hap_ty, ty);
    let ty = pi_over(k, W_FV, c.mc, ty);
    let ty = pi_over(k, V_FV, c.mc, ty);
    let ty = pi_over(k, A_FV, c.fc, ty);
    let ty = pi_over(k, HM_FV, hm_ty, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(ns, "smul_left_cancel");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.VectorSpace.solve_smul : forall F M smul, IsVectorSpace F M smul ->
/// forall a v w, F.apart a F.zero -> M.equiv (smul a v) w ->
/// Exists (fun c => M.equiv v (smul c w))`.
///
/// **Solving for a coefficient** — the atomic Steinitz exchange step, and the
/// one place a vector-space proof genuinely needs the field rather than the
/// ring. The witness is the inverse the field's `mulInvEx` supplies, which
/// never leaves the `Prop`.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_solve_smul(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fr: &RecordNames,
    cg: &RecordNames,
    to_comm_ring: NameId,
    is_vector_space: NameId,
    mn: &ModuleNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = vctx(k, fr, cg, to_comm_ring);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let hm_ty = {
        let t = k.const_(is_vector_space, vec![]);
        t_app(k, t, &[c.f, c.m, c.smul])
    };
    let hm = k.fvar(HM_FV);
    let a = k.fvar(A_FV);
    let v = k.fvar(V_FV);
    let w = k.fvar(W_FV);
    let hap_ty = app2(k, c.fapart, a, c.fzero);
    let a_v = c.act(k, a, v);
    let heq_ty = c.meqv(k, a_v, w);
    let hap = k.fvar(H1_FV);
    let heq = k.fvar(H2_FV);

    // `goal := Exists F.carrier (fun c => M.equiv v (smul c w))`.
    let goal_pred = {
        let cc = k.fvar(C_FV);
        let cw = c.act(k, cc, w);
        let body = c.meqv(k, v, cw);
        lam_over(k, C_FV, c.fc, body)
    };
    let ex = k.const_(lg.exists_, vec![l1]);
    let goal = app2(k, ex, c.fc, goal_pred);

    let pred = {
        let bb = k.fvar(B_FV);
        let abb = c.ftimes(k, a, bb);
        let body = c.feqv(k, abb, c.fone);
        lam_over(k, B_FV, c.fc, body)
    };
    let ex_ty = app2(k, ex, c.fc, pred);
    let motive = lam_over(k, SCRATCH_FV, ex_ty, goal);
    let witness = t_app(k, c.fmul_inv_ex, &[a, hap]);

    let minor = {
        let b = k.fvar(B_FV);
        let ab = c.ftimes(k, a, b);
        let hb_ty = c.feqv(k, ab, c.fone);
        let hb = k.fvar(H3_FV);
        let chain = inv_chain(
            k,
            &c,
            mn.one_smul,
            mn.mul_smul,
            mn.smul_congr,
            hm,
            a,
            b,
            v,
            hb,
        );
        // `b•(a•v) ~ b•w` from `heq : a•v ~ w`.
        let step = {
            let t = k.const_(mn.smul_congr, vec![]);
            let app = t_app(k, t, &[c.ring, c.m, c.smul, hm]);
            let rb = k.app(c.frefl, b);
            t_app(k, app, &[b, b, a_v, w, rb, heq])
        };
        let bw = c.act(k, b, w);
        let full = c.mtr(k, v, chain.b_av, bw, chain.to_b_av, step);
        let intro = k.const_(lg.exists_intro, vec![l1]);
        let body = t_app(k, intro, &[c.fc, goal_pred, b, full]);
        let inner = lam_over(k, H3_FV, hb_ty, body);
        lam_over(k, B_FV, c.fc, inner)
    };
    let rec = k.const_(lg.exists_rec, vec![l1]);
    let proof = t_app(k, rec, &[c.fc, pred, motive, minor, witness]);

    let value = lam_over(k, H2_FV, heq_ty, proof);
    let value = lam_over(k, H1_FV, hap_ty, value);
    let value = lam_over(k, W_FV, c.mc, value);
    let value = lam_over(k, V_FV, c.mc, value);
    let value = lam_over(k, A_FV, c.fc, value);
    let value = lam_over(k, HM_FV, hm_ty, value);
    let value = c.close_lam(k, value);

    let ty = arrow(k, heq_ty, goal);
    let ty = arrow(k, hap_ty, ty);
    let ty = pi_over(k, W_FV, c.mc, ty);
    let ty = pi_over(k, V_FV, c.mc, ty);
    let ty = pi_over(k, A_FV, c.fc, ty);
    let ty = pi_over(k, HM_FV, hm_ty, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(ns, "solve_smul");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// Dimension, at zero.
// ---------------------------------------------------------------------------

/// `AlgS.VectorSpace.basis_zero_unique : forall F M smul (v u : Nat ->
/// M.carrier) (m : Nat), AlgS.Module.isBasis (toCommRing F) M smul v Nat.zero
/// -> AlgS.Module.isBasis (toCommRing F) M smul u m -> Eq Nat m Nat.zero`.
///
/// **Invariance of basis number at zero** — the first dimension statement in
/// this library. See the module doc for why it takes no `IsVectorSpace`
/// hypothesis and for what the general theorem costs.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_basis_zero_unique(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fr: &RecordNames,
    cg: &RecordNames,
    to_comm_ring: NameId,
    mn: &ModuleNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = vctx(k, fr, cg, to_comm_ring);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let nat = k.const_(lg.nat, vec![]);
    let nat_zero = k.const_(lg.nat_zero, vec![]);
    let nat_succ = k.const_(lg.nat_succ, vec![]);
    let vec_ty = arrow(k, nat, c.mc);
    let coeff_ty = arrow(k, nat, c.fc);

    let v = k.fvar(V_FV);
    let u = k.fvar(U_FV);
    let n = k.fvar(N_FV);

    let basis_at = |k: &mut Kernel, fam: ExprId, len: ExprId| {
        let t = k.const_(mn.is_basis, vec![]);
        t_app(k, t, &[c.ring, c.m, c.smul, fam, len])
    };
    let spans_at = |k: &mut Kernel, fam: ExprId, len: ExprId| {
        let t = k.const_(mn.spans, vec![]);
        t_app(k, t, &[c.ring, c.m, c.smul, fam, len])
    };
    let indep_at = |k: &mut Kernel, fam: ExprId, len: ExprId| {
        let t = k.const_(mn.linear_independent, vec![]);
        t_app(k, t, &[c.ring, c.m, c.smul, fam, len])
    };
    let lin_comb_at = |k: &mut Kernel, coeff: ExprId, fam: ExprId, len: ExprId| {
        let t = k.const_(mn.lin_comb, vec![]);
        t_app(k, t, &[c.ring, c.m, c.smul, coeff, fam, len])
    };

    let hbv_ty = basis_at(k, v, nat_zero);
    let hbu_ty = basis_at(k, u, n);
    let hbv = k.fvar(H1_FV);
    let hbu = k.fvar(H2_FV);

    // `triv : forall w, M.equiv M.e w`, from `spans v 0`.
    let (triv, triv_ty) = {
        let sp_v = spans_at(k, v, nat_zero);
        let li_v = indep_at(k, v, nat_zero);
        let and_left = k.const_(lg.and_left, vec![]);
        let sp = t_app(k, and_left, &[sp_v, li_v, hbv]); // spans v 0
        let w = k.fvar(W_FV);
        let sp_w = k.app(sp, w); // Exists c, M.equiv (linComb c v 0) w
        let pred = {
            let cc = k.fvar(C_FV);
            let lc = lin_comb_at(k, cc, v, nat_zero);
            let body = c.meqv(k, lc, w);
            lam_over(k, C_FV, coeff_ty, body)
        };
        let ex = k.const_(lg.exists_, vec![l1]);
        let ex_ty = app2(k, ex, coeff_ty, pred);
        let goal = c.meqv(k, c.me, w);
        let motive = lam_over(k, SCRATCH_FV, ex_ty, goal);
        // `linComb R M smul c v 0` ι-reduces to `M.e`, so the hypothesis IS
        // the goal and the minor premise is the identity.
        let minor = {
            let hc = k.fvar(H3_FV);
            let inner = lam_over(k, H3_FV, goal, hc);
            lam_over(k, C_FV, coeff_ty, inner)
        };
        let rec = k.const_(lg.exists_rec, vec![l1]);
        let body = t_app(k, rec, &[coeff_ty, pred, motive, minor, sp_w]);
        let value = lam_over(k, W_FV, c.mc, body);
        let ty = pi_over(k, W_FV, c.mc, goal);
        (value, ty)
    };
    let triv_fv = k.fvar(SCRATCH_FV + 1);

    // The `Nat.rec` motive: `fun j => isBasis u j -> Eq Nat j Nat.zero`.
    let motive = {
        let j = k.fvar(J_FV);
        let hb = basis_at(k, u, j);
        let concl = eq_of(k, lg, l1, nat, j, nat_zero);
        let body = arrow(k, hb, concl);
        lam_over(k, J_FV, nat, body)
    };
    let minor_zero = {
        let hb = basis_at(k, u, nat_zero);
        let r = refl_of(k, lg, l1, nat, nat_zero);
        lam_over(k, H3_FV, hb, r)
    };
    let minor_succ = {
        let j = k.fvar(J_FV);
        let sj = k.app(nat_succ, j);
        let ih_ty = {
            let hb = basis_at(k, u, j);
            let concl = eq_of(k, lg, l1, nat, j, nat_zero);
            arrow(k, hb, concl)
        };
        let hb_ty = basis_at(k, u, sj);
        let hb = k.fvar(H3_FV);

        let sp_u = spans_at(k, u, sj);
        let li_u = indep_at(k, u, sj);
        let and_right = k.const_(lg.and_right, vec![]);
        let li = t_app(k, and_right, &[sp_u, li_u, hb]); // linearIndependent u (succ j)

        let cone = lam_over(k, SCRATCH_FV, nat, c.fone);
        let czero = lam_over(k, SCRATCH_FV, nat, c.fzero);
        let l_one = lin_comb_at(k, cone, u, sj);
        let l_zero = lin_comb_at(k, czero, u, sj);
        // Both combinations are `M.e` up to `~`, so they are `~` each other.
        let t_one = k.app(triv_fv, l_one); // M.e ~ L1
        let t_zero = k.app(triv_fv, l_zero); // M.e ~ L0
        let flip = c.msy(k, c.me, l_one, t_one); // L1 ~ M.e
        let hyp = c.mtr(k, l_one, c.me, l_zero, flip, t_zero);

        let ca = t_app(k, li, &[cone, czero, hyp]); // coeffAgree R cone czero (succ j)
        let head = {
            let t = k.const_(mn.coeff_agree, vec![]);
            t_app(k, t, &[c.ring, cone, czero, j])
        };
        let tail = c.feqv(k, c.fone, c.fzero);
        let and_right2 = k.const_(lg.and_right, vec![]);
        let one_eq_zero = t_app(k, and_right2, &[head, tail, ca]);
        let bad = t_app(
            k,
            c.fapart_compat,
            &[c.fone, c.fzero, one_eq_zero],
        );
        let one_apart_zero = sel(k, fr, ix::ONE_APART_ZERO, c.f);
        let contradiction = k.app(bad, one_apart_zero);

        let false_ty = k.const_(lg.false_, vec![]);
        let concl = eq_of(k, lg, l1, nat, sj, nat_zero);
        let false_motive = lam_over(k, SCRATCH_FV, false_ty, concl);
        let false_rec = k.const_(lg.false_rec, vec![l0]);
        let body = t_app(k, false_rec, &[false_motive, contradiction]);

        let inner = lam_over(k, H3_FV, hb_ty, body);
        let inner = lam_over(k, IH_FV, ih_ty, inner);
        lam_over(k, J_FV, nat, inner)
    };
    let nat_rec = k.const_(lg.nat_rec, vec![l0]);
    let cased = t_app(k, nat_rec, &[motive, minor_zero, minor_succ, n]);
    let applied = k.app(cased, hbu);

    // Bind `triv` with a `let`-free beta redex: `(fun triv => …) <proof>`.
    let body = lam_over(k, SCRATCH_FV + 1, triv_ty, applied);
    let proof = k.app(body, triv);

    let value = lam_over(k, H2_FV, hbu_ty, proof);
    let value = lam_over(k, H1_FV, hbv_ty, value);
    let value = lam_over(k, N_FV, nat, value);
    let value = lam_over(k, U_FV, vec_ty, value);
    let value = lam_over(k, V_FV, vec_ty, value);
    let value = c.close_lam(k, value);

    let concl = eq_of(k, lg, l1, nat, n, nat_zero);
    let ty = arrow(k, hbu_ty, concl);
    let ty = arrow(k, hbv_ty, ty);
    let ty = pi_over(k, N_FV, nat, ty);
    let ty = pi_over(k, U_FV, vec_ty, ty);
    let ty = pi_over(k, V_FV, vec_ty, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(ns, "basis_zero_unique");
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VectorSpaceNames {
    pub is_vector_space: NameId,
    pub smul_left_cancel: NameId,
    pub solve_smul: NameId,
    pub basis_zero_unique: NameId,
}

#[cfg(test)]
impl VectorSpaceNames {
    #[must_use]
    pub fn all(&self) -> [NameId; 4] {
        [
            self.is_vector_space,
            self.smul_left_cancel,
            self.solve_smul,
            self.basis_zero_unique,
        ]
    }
}

/// Declare `AlgS.VectorSpace.*`. Needs the `AlgS.Field` record and
/// `toCommRing` from [`super::field_setoid`], `AlgS.CommGroup`, and
/// `AlgS.Module.*`'s own names.
pub(crate) fn declare_vector_space(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fn_: &FieldNames,
    cg: &RecordNames,
    mn: &ModuleNames,
    algs: NameId,
) -> Result<VectorSpaceNames, KernelError> {
    let ns = k.name_str(algs, "VectorSpace");
    let fr = &fn_.field;
    let is_vector_space =
        declare_is_vector_space(k, fr, cg, fn_.to_comm_ring, mn.is_module, ns)?;
    let smul_left_cancel = declare_smul_left_cancel(
        k,
        lg,
        fr,
        cg,
        fn_.to_comm_ring,
        is_vector_space,
        mn,
        ns,
    )?;
    let solve_smul =
        declare_solve_smul(k, lg, fr, cg, fn_.to_comm_ring, is_vector_space, mn, ns)?;
    let basis_zero_unique =
        declare_basis_zero_unique(k, lg, fr, cg, fn_.to_comm_ring, mn, ns)?;

    Ok(VectorSpaceNames {
        is_vector_space,
        smul_left_cancel,
        solve_smul,
        basis_zero_unique,
    })
}

#[cfg(test)]
#[path = "vector_space_tests.rs"]
mod vector_space_tests;
