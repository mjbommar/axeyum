//! `AlgS.Module.*` — roadmap W3-2: modules (and hence vector spaces) over an
//! **abstract** `AlgS.CommRing`, built by the setoid route (ADR-1595,
//! ADR-1609), with `R[X]` and `R`-over-itself as the first two instances.
//!
//! # Why a predicate and not a record
//!
//! A module is a triple: a scalar ring `R`, an abelian group `M`, and an
//! action `smul : R.carrier -> M.carrier -> M.carrier`. A RECORD holding that
//! triple cannot be built with [`super::structures::declare_record`], and the
//! obstruction is a **universe** one, not a quotient one:
//! `declare_record` admits a parameterless inductive at `Sort 2` whose
//! constructor fields are `CarrierSort` (`Sort 1`), `Data` (`Sort 1`) or
//! `Law` (`Sort 0`) — one fixed level per kind. A `ring : AlgS.CommRing`
//! field lives in `Sort 2`, which would push the record itself to `Sort 3`
//! and, with the levels shifted wholesale, would put the module's own carrier
//! at `Sort 2` — where `Nat -> R.carrier` (a `Sort 1`) can no longer sit,
//! since this kernel's `Sort` hierarchy is not cumulative. Supporting it needs
//! a per-field level on `FieldSpec`, which is a change to the shared `Alg`
//! machinery and out of scope here (ADR-1609 sizes it).
//!
//! So this module follows `AlgS.Hom.*`'s own answer to the same problem
//! (ADR-1595): carry the data as **explicit arguments** and the axioms as a
//! **`Prop`**. [`declare_is_module`] is that `Prop`, a five-fold `And` whose
//! first conjunct is the congruence obligation the setoid discipline makes
//! explicit — `Eq` would supply it free, `equiv` does not.
//!
//! # What is declared
//!
//! | name | kind | what it is |
//! |---|---|---|
//! | `AlgS.idem_eq_e` | theorem | in any `AlgS.Group`, `x ~ x·x` forces `x ~ e` |
//! | `AlgS.Module.smulCongrP` | definition | the congruence axiom, as a `Prop` |
//! | `AlgS.Module.smulAddP` | definition | `a•(v+w) ~ a•v + a•w` |
//! | `AlgS.Module.addSmulP` | definition | `(a+b)•v ~ a•v + b•v` |
//! | `AlgS.Module.mulSmulP` | definition | `(a·b)•v ~ a•(b•v)` |
//! | `AlgS.Module.oneSmulP` | definition | `1•v ~ v` |
//! | `AlgS.Module.IsModule` | definition | the conjunction of the five |
//! | `AlgS.Module.smulCongr` … `oneSmul` | theorems | the five accessors |
//! | `AlgS.Module.smul_zero` | theorem | `a•0 ~ 0` |
//! | `AlgS.Module.zero_smul` | theorem | `0•v ~ 0` |
//! | `AlgS.Module.neg_smul` | theorem | `(−a)•v ~ −(a•v)` |
//! | `AlgS.Module.selfModule` | theorem | **`R` is a module over itself** |
//! | `AlgS.Module.polyModule` | theorem | **`R[X]` is a module over `R`** |
//! | `AlgS.Module.linComb` | definition | `Σ_{i<n} c i • v i` |
//! | `AlgS.Module.coeffAgree` | definition | two coefficient functions agree below `n` |
//! | `AlgS.Module.spans` | definition | every vector is such a combination |
//! | `AlgS.Module.linearIndependent` | definition | the coordinate map is injective |
//! | `AlgS.Module.isBasis` | definition | spanning and independent |
//! | `AlgS.Module.linComb_congr` | theorem | agreeing coefficients give equivalent combinations |
//!
//! `coeffAgree` exists because `Nat.lt` does not: at the `AlgS` build
//! position only `Nat`, `Nat.zero`, `Nat.succ` and `Nat.rec` are declared, so
//! "the coefficients below `n`" is built by structural recursion on `n`
//! rather than as `forall i, i < n -> …`.
//!
//! # Where this stops
//!
//! **Dimension is not here.** `isBasis` is stated, and `linComb_congr` proves
//! the easy half of independence, but the invariance of basis number needs a
//! FIELD — an `AlgS.CommRing` with inverses — and `AlgS.Field` does not
//! exist: ADR-1588 stopped short of it because a constructive field needs an
//! apartness relation, and ADR-1595 recorded that as a separate open
//! question. That is the gate on "vector spaces" as opposed to "modules", and
//! it is unrelated to `Quot.sound`.

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

use super::structures::{RecordNames, app2, arrow, lam_over, pi_over, sel};
use super::structures_setoid::idx;

// ---------------------------------------------------------------------------
// Free-variable block, disjoint from `structures_setoid` (21_xxx) and
// `polynomial_setoid` (22_xxx).
// ---------------------------------------------------------------------------

const R_FV: u64 = 23_000;
const M_FV: u64 = 23_001;
const SM_FV: u64 = 23_002;
const HM_FV: u64 = 23_003;
const G_FV: u64 = 23_004;
const A_FV: u64 = 23_010;
const AP_FV: u64 = 23_011;
const B_FV: u64 = 23_012;
const V_FV: u64 = 23_013;
const VP_FV: u64 = 23_014;
const W_FV: u64 = 23_015;
const X_FV: u64 = 23_016;
const H1_FV: u64 = 23_020;
const H2_FV: u64 = 23_021;
const C_FV: u64 = 23_030;
const D_FV: u64 = 23_031;
const VEC_FV: u64 = 23_032;
const N_FV: u64 = 23_040;
const J_FV: u64 = 23_041;
const IH_FV: u64 = 23_042;
const SCRATCH_FV: u64 = 23_050;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

// ---------------------------------------------------------------------------
// The scalar ring / vector group selector bundle.
// ---------------------------------------------------------------------------

struct MCtx {
    /// `R : AlgS.CommRing`, as a free variable, and its record type.
    r: ExprId,
    ring_ty: ExprId,
    rc: ExprId,
    req: ExprId,
    rrefl: ExprId,
    rzero: ExprId,
    rone: ExprId,
    radd: ExprId,
    rmul: ExprId,
    radd_zero: ExprId,
    rneg: ExprId,
    rneg_add: ExprId,
    /// `M : AlgS.CommGroup`, as a free variable, and its record type.
    m: ExprId,
    group_ty: ExprId,
    mc: ExprId,
    meq: ExprId,
    mrefl: ExprId,
    msymm: ExprId,
    mtrans: ExprId,
    mop: ExprId,
    mop_congr: ExprId,
    me: ExprId,
    minv: ExprId,
    minv_r: ExprId,
    mcomm: ExprId,
    /// `smul : R.carrier -> M.carrier -> M.carrier`, as a free variable, and
    /// its type.
    smul: ExprId,
    smul_ty: ExprId,
}

fn mctx(k: &mut Kernel, cr: &RecordNames, cg: &RecordNames) -> MCtx {
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
    MCtx {
        r: rv,
        ring_ty,
        rc,
        req: sel(k, cr, r::EQUIV, rv),
        rrefl: sel(k, cr, r::EQUIV_REFL, rv),
        rzero: sel(k, cr, r::ZERO, rv),
        rone: sel(k, cr, r::ONE, rv),
        radd: sel(k, cr, r::ADD, rv),
        rmul: sel(k, cr, r::MUL, rv),
        radd_zero: sel(k, cr, r::ADD_ZERO, rv),
        rneg: sel(k, cr, r::NEG, rv),
        rneg_add: sel(k, cr, r::NEG_ADD, rv),
        m: mv,
        group_ty,
        mc,
        meq: sel(k, cg, g::EQUIV, mv),
        mrefl: sel(k, cg, g::EQUIV_REFL, mv),
        msymm: sel(k, cg, g::EQUIV_SYMM, mv),
        mtrans: sel(k, cg, g::EQUIV_TRANS, mv),
        mop: sel(k, cg, g::OP, mv),
        mop_congr: sel(k, cg, g::OP_CONGR, mv),
        me: sel(k, cg, g::E, mv),
        minv: sel(k, cg, g::INV, mv),
        minv_r: sel(k, cg, g::INV_R, mv),
        mcomm: sel(k, cg, g::COMM, mv),
        smul: k.fvar(SM_FV),
        smul_ty,
    }
}

impl MCtx {
    fn meqv(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.meq, a, b)
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
    fn mplus(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.mop, a, b)
    }
    fn act(&self, k: &mut Kernel, a: ExprId, v: ExprId) -> ExprId {
        app2(k, self.smul, a, v)
    }
    /// `forall (R : CommRing) (M : CommGroup) (smul : …), <body>`.
    fn close_pi(&self, k: &mut Kernel, body: ExprId) -> ExprId {
        let t = pi_over(k, SM_FV, self.smul_ty, body);
        let t = pi_over(k, M_FV, self.group_ty, t);
        pi_over(k, R_FV, self.ring_ty, t)
    }
    /// `fun (R : CommRing) (M : CommGroup) (smul : …) => <body>`.
    fn close_lam(&self, k: &mut Kernel, body: ExprId) -> ExprId {
        let t = lam_over(k, SM_FV, self.smul_ty, body);
        let t = lam_over(k, M_FV, self.group_ty, t);
        lam_over(k, R_FV, self.ring_ty, t)
    }
}

// ---------------------------------------------------------------------------
// `AlgS.idem_eq_e` — the group lemma both `smul_zero` and `zero_smul` reduce
// to, stated over `AlgS.Group` so it is reusable off the module shelf.
// ---------------------------------------------------------------------------

/// `AlgS.idem_eq_e : forall (G : AlgS.Group) (x : G.carrier),
/// G.equiv x (G.op x x) -> G.equiv x G.e`.
///
/// `x·e ~ x ~ x·x`, then `AlgS.add_left_cancel` on the left factor gives
/// `e ~ x`, symm'd. Three steps.
fn declare_idem_eq_e(
    k: &mut Kernel,
    group: &RecordNames,
    add_left_cancel: NameId,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    use idx::group::{CARRIER, E, EQUIV, EQUIV_SYMM, EQUIV_TRANS, IDENT_R, OP};
    let group_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(G_FV);
    let carrier = sel(k, group, CARRIER, g);
    let equiv = sel(k, group, EQUIV, g);
    let equiv_symm = sel(k, group, EQUIV_SYMM, g);
    let equiv_trans = sel(k, group, EQUIV_TRANS, g);
    let op = sel(k, group, OP, g);
    let e = sel(k, group, E, g);
    let ident_r = sel(k, group, IDENT_R, g);

    let x = k.fvar(X_FV);
    let xx = app2(k, op, x, x);
    let hyp_ty = app2(k, equiv, x, xx);
    let h = k.fvar(H1_FV);

    let x_e = app2(k, op, x, e);
    let ir = k.app(ident_r, x); // equiv (op x e) x
    let chain = t_app(k, equiv_trans, &[x_e, x, xx, ir, h]); // equiv (op x e) (op x x)
    let cancel = {
        let t = k.const_(add_left_cancel, vec![]);
        t_app(k, t, &[g, x, e, x, chain]) // equiv e x
    };
    let proof = t_app(k, equiv_symm, &[e, x, cancel]); // equiv x e

    let value = lam_over(k, H1_FV, hyp_ty, proof);
    let value = lam_over(k, X_FV, carrier, value);
    let value = lam_over(k, G_FV, group_ty, value);

    let concl = app2(k, equiv, x, e);
    let ty = pi_over(k, H1_FV, hyp_ty, concl);
    let ty = pi_over(k, X_FV, carrier, ty);
    let ty = pi_over(k, G_FV, group_ty, ty);

    let name = k.name_str(algs_p, "idem_eq_e");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// The five module axioms as `Prop`s, and their conjunction.
// ---------------------------------------------------------------------------

/// Declare one axiom predicate: `forall R M smul, Prop`, whose value is the
/// statement `body` builds from the context.
fn declare_axiom_pred(
    k: &mut Kernel,
    cr: &RecordNames,
    cg: &RecordNames,
    ns: NameId,
    suffix: &str,
    body: &dyn Fn(&mut Kernel, &MCtx) -> ExprId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let stmt = body(k, &c);
    let value = c.close_lam(k, stmt);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = c.close_pi(k, prop);

    let name = k.name_str(ns, suffix);
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `forall a a' v v', R.equiv a a' -> M.equiv v v' ->
/// M.equiv (smul a v) (smul a' v')` — **the congruence obligation**. On the
/// `Eq` spine this field does not exist; here it is axiom number one.
fn smul_congr_stmt(k: &mut Kernel, c: &MCtx) -> ExprId {
    let a = k.fvar(A_FV);
    let ap = k.fvar(AP_FV);
    let v = k.fvar(V_FV);
    let vp = k.fvar(VP_FV);
    let hyp1 = app2(k, c.req, a, ap);
    let hyp2 = c.meqv(k, v, vp);
    let lhs = c.act(k, a, v);
    let rhs = c.act(k, ap, vp);
    let concl = c.meqv(k, lhs, rhs);
    let t = pi_over(k, H2_FV, hyp2, concl);
    let t = pi_over(k, H1_FV, hyp1, t);
    let t = pi_over(k, VP_FV, c.mc, t);
    let t = pi_over(k, V_FV, c.mc, t);
    let t = pi_over(k, AP_FV, c.rc, t);
    pi_over(k, A_FV, c.rc, t)
}

/// `forall a v w, M.equiv (smul a (M.op v w)) (M.op (smul a v) (smul a w))`.
fn smul_add_stmt(k: &mut Kernel, c: &MCtx) -> ExprId {
    let a = k.fvar(A_FV);
    let v = k.fvar(V_FV);
    let w = k.fvar(W_FV);
    let vw = c.mplus(k, v, w);
    let lhs = c.act(k, a, vw);
    let av = c.act(k, a, v);
    let aw = c.act(k, a, w);
    let rhs = c.mplus(k, av, aw);
    let concl = c.meqv(k, lhs, rhs);
    let t = pi_over(k, W_FV, c.mc, concl);
    let t = pi_over(k, V_FV, c.mc, t);
    pi_over(k, A_FV, c.rc, t)
}

/// `forall a b v, M.equiv (smul (R.add a b) v) (M.op (smul a v) (smul b v))`.
fn add_smul_stmt(k: &mut Kernel, c: &MCtx) -> ExprId {
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let v = k.fvar(V_FV);
    let ab = app2(k, c.radd, a, b);
    let lhs = c.act(k, ab, v);
    let av = c.act(k, a, v);
    let bv = c.act(k, b, v);
    let rhs = c.mplus(k, av, bv);
    let concl = c.meqv(k, lhs, rhs);
    let t = pi_over(k, V_FV, c.mc, concl);
    let t = pi_over(k, B_FV, c.rc, t);
    pi_over(k, A_FV, c.rc, t)
}

/// `forall a b v, M.equiv (smul (R.mul a b) v) (smul a (smul b v))`.
fn mul_smul_stmt(k: &mut Kernel, c: &MCtx) -> ExprId {
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let v = k.fvar(V_FV);
    let ab = app2(k, c.rmul, a, b);
    let lhs = c.act(k, ab, v);
    let bv = c.act(k, b, v);
    let rhs = c.act(k, a, bv);
    let concl = c.meqv(k, lhs, rhs);
    let t = pi_over(k, V_FV, c.mc, concl);
    let t = pi_over(k, B_FV, c.rc, t);
    pi_over(k, A_FV, c.rc, t)
}

/// `forall v, M.equiv (smul R.one v) v`.
fn one_smul_stmt(k: &mut Kernel, c: &MCtx) -> ExprId {
    let v = k.fvar(V_FV);
    let lhs = c.act(k, c.rone, v);
    let concl = c.meqv(k, lhs, v);
    pi_over(k, V_FV, c.mc, concl)
}

/// The five axiom names, in conjunction order. The shared `P` suffix is the
/// point -- it distinguishes the axiom PROPOSITION from the accessor theorem
/// of the same name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(clippy::struct_field_names)]
struct AxiomNames {
    smul_congr_p: NameId,
    smul_add_p: NameId,
    add_smul_p: NameId,
    mul_smul_p: NameId,
    one_smul_p: NameId,
}

impl AxiomNames {
    fn in_order(self) -> [NameId; 5] {
        [
            self.smul_congr_p,
            self.smul_add_p,
            self.add_smul_p,
            self.mul_smul_p,
            self.one_smul_p,
        ]
    }
}

/// `AlgS.Module.IsModule R M smul :=
/// And (smulCongrP …) (And (smulAddP …) (And (addSmulP …)
///   (And (mulSmulP …) (oneSmulP …))))` — right-nested, so the accessors
/// below are `And.left` after `k` many `And.right`s.
fn declare_is_module(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    ax: AxiomNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let parts: Vec<ExprId> = ax
        .in_order()
        .iter()
        .map(|n| {
            let t = k.const_(*n, vec![]);
            t_app(k, t, &[c.r, c.m, c.smul])
        })
        .collect();
    let and_c = k.const_(lg.and, vec![]);
    let mut body = parts[4];
    for part in parts[..4].iter().rev() {
        body = app2(k, and_c, *part, body);
    }
    let value = c.close_lam(k, body);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = c.close_pi(k, prop);

    let name = k.name_str(ns, "IsModule");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;
    Ok(name)
}

/// One accessor: `forall R M smul, IsModule R M smul -> <axiom i>`, proved by
/// `i` applications of `And.right` followed by `And.left` (or, for the last
/// axiom, four `And.right`s).
#[allow(clippy::too_many_arguments)]
fn declare_accessor(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    is_module: NameId,
    ax: AxiomNames,
    which: usize,
    suffix: &str,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let parts: Vec<ExprId> = ax
        .in_order()
        .iter()
        .map(|n| {
            let t = k.const_(*n, vec![]);
            t_app(k, t, &[c.r, c.m, c.smul])
        })
        .collect();
    // `tails[i]` is the proposition remaining after `i` `And.right`s.
    let mut tails = vec![parts[4]];
    for part in parts[..4].iter().rev() {
        let last = *tails.last().expect("non-empty");
        let and_c = k.const_(lg.and, vec![]);
        tails.push(app2(k, and_c, *part, last));
    }
    tails.reverse(); // tails[0] is the whole conjunction

    let hyp_ty = {
        let t = k.const_(is_module, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul])
    };
    let h = k.fvar(HM_FV);
    let and_right = k.const_(lg.and_right, vec![]);
    let and_left = k.const_(lg.and_left, vec![]);

    let mut cur = h;
    for i in 0..which {
        let a = parts[i];
        let b = tails[i + 1];
        cur = t_app(k, and_right, &[a, b, cur]);
    }
    let proof = if which == 4 {
        cur
    } else {
        let a = parts[which];
        let b = tails[which + 1];
        t_app(k, and_left, &[a, b, cur])
    };

    let value = lam_over(k, HM_FV, hyp_ty, proof);
    let value = c.close_lam(k, value);
    let ty = pi_over(k, HM_FV, hyp_ty, parts[which]);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(ns, suffix);
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// The three generic module theorems.
// ---------------------------------------------------------------------------

/// Names of the five accessors, so the theorems below apply them by name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AccessorNames {
    smul_congr: NameId,
    #[allow(dead_code)]
    smul_add: NameId,
    add_smul: NameId,
    #[allow(dead_code)]
    mul_smul: NameId,
    #[allow(dead_code)]
    one_smul: NameId,
}

/// Shared tail of `smul_zero`/`zero_smul`: from `hx : M.equiv x (M.op x x)`,
/// conclude `M.equiv x M.e` by `AlgS.idem_eq_e` at `AlgS.CommGroup.toGroupS M`.
fn idem_tail(
    k: &mut Kernel,
    c: &MCtx,
    idem: NameId,
    to_group: NameId,
    x: ExprId,
    hx: ExprId,
) -> ExprId {
    let tg = k.const_(to_group, vec![]);
    let g = k.app(tg, c.m);
    let t = k.const_(idem, vec![]);
    t_app(k, t, &[g, x, hx])
}

/// `AlgS.Module.smul_zero : forall R M smul, IsModule R M smul ->
/// forall a, M.equiv (smul a M.e) M.e`.
///
/// `a•0 ~ a•(0+0) ~ a•0 + a•0`, then `AlgS.idem_eq_e`.
#[allow(clippy::too_many_arguments)]
fn declare_smul_zero(
    k: &mut Kernel,
    cr: &RecordNames,
    cg: &RecordNames,
    is_module: NameId,
    acc: AccessorNames,
    smul_add_acc: NameId,
    idem: NameId,
    to_group: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use idx::comm_group::IDENT_L;
    let c = mctx(k, cr, cg);
    let m_ident_l = sel(k, cg, IDENT_L, c.m);

    let hyp_ty = {
        let t = k.const_(is_module, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul])
    };
    let hm = k.fvar(HM_FV);
    let sc = {
        let t = k.const_(acc.smul_congr, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, hm])
    };
    let sa = {
        let t = k.const_(smul_add_acc, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, hm])
    };

    let a = k.fvar(A_FV);
    let x = c.act(k, a, c.me); // x := a • 0
    let ee = c.mplus(k, c.me, c.me);
    let a_ee = c.act(k, a, ee);

    let ident_l_e = k.app(m_ident_l, c.me); // equiv (op e e) e
    let refl_a = k.app(c.rrefl, a);
    let step1 = t_app(k, sc, &[a, a, ee, c.me, refl_a, ident_l_e]); // a•(e+e) ~ a•e
    let step1s = c.msy(k, a_ee, x, step1); // a•e ~ a•(e+e)
    let step2 = t_app(k, sa, &[a, c.me, c.me]); // a•(e+e) ~ a•e + a•e
    let xx = c.mplus(k, x, x);
    let hx = c.mtr(k, x, a_ee, xx, step1s, step2);
    let proof = idem_tail(k, &c, idem, to_group, x, hx);

    let value = lam_over(k, A_FV, c.rc, proof);
    let value = lam_over(k, HM_FV, hyp_ty, value);
    let value = c.close_lam(k, value);

    let concl = c.meqv(k, x, c.me);
    let ty = pi_over(k, A_FV, c.rc, concl);
    let ty = pi_over(k, HM_FV, hyp_ty, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(ns, "smul_zero");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Module.zero_smul : forall R M smul, IsModule R M smul ->
/// forall v, M.equiv (smul R.zero v) M.e`.
///
/// `0•v ~ (0+0)•v ~ 0•v + 0•v`, then `AlgS.idem_eq_e`. Same shape as
/// [`declare_smul_zero`] with the idempotence coming from `R.addZero R.zero`
/// instead of `M.identL M.e`.
#[allow(clippy::too_many_arguments)]
fn declare_zero_smul(
    k: &mut Kernel,
    cr: &RecordNames,
    cg: &RecordNames,
    is_module: NameId,
    acc: AccessorNames,
    idem: NameId,
    to_group: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let hyp_ty = {
        let t = k.const_(is_module, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul])
    };
    let hm = k.fvar(HM_FV);
    let sc = {
        let t = k.const_(acc.smul_congr, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, hm])
    };
    let as_ = {
        let t = k.const_(acc.add_smul, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, hm])
    };

    let v = k.fvar(V_FV);
    let y = c.act(k, c.rzero, v); // y := 0 • v
    let zz = app2(k, c.radd, c.rzero, c.rzero);
    let zz_v = c.act(k, zz, v);

    let add_zero_z = k.app(c.radd_zero, c.rzero); // R.equiv (0+0) 0
    let refl_v = k.app(c.mrefl, v);
    let step1 = t_app(k, sc, &[zz, c.rzero, v, v, add_zero_z, refl_v]); // (0+0)•v ~ 0•v
    let step1s = c.msy(k, zz_v, y, step1);
    let step2 = t_app(k, as_, &[c.rzero, c.rzero, v]); // (0+0)•v ~ 0•v + 0•v
    let yy = c.mplus(k, y, y);
    let hy = c.mtr(k, y, zz_v, yy, step1s, step2);
    let proof = idem_tail(k, &c, idem, to_group, y, hy);

    let value = lam_over(k, V_FV, c.mc, proof);
    let value = lam_over(k, HM_FV, hyp_ty, value);
    let value = c.close_lam(k, value);

    let concl = c.meqv(k, y, c.me);
    let ty = pi_over(k, V_FV, c.mc, concl);
    let ty = pi_over(k, HM_FV, hyp_ty, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(ns, "zero_smul");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Module.neg_smul : forall R M smul, IsModule R M smul ->
/// forall a v, M.equiv (smul (R.neg a) v) (M.inv (smul a v))`.
///
/// `a•v + (−a)•v ~ (a + −a)•v ~ 0•v ~ 0`, so `(−a)•v` is a right inverse of
/// `a•v`; `AlgS.inv_unique` (through `M.comm` to get the left-sided form)
/// identifies it with `M.inv (a•v)`.
#[allow(clippy::too_many_arguments)]
fn declare_neg_smul(
    k: &mut Kernel,
    cr: &RecordNames,
    cg: &RecordNames,
    is_module: NameId,
    acc: AccessorNames,
    zero_smul: NameId,
    inv_unique: NameId,
    to_group: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let hyp_ty = {
        let t = k.const_(is_module, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul])
    };
    let hm = k.fvar(HM_FV);
    let sc = {
        let t = k.const_(acc.smul_congr, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, hm])
    };
    let as_ = {
        let t = k.const_(acc.add_smul, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, hm])
    };

    let a = k.fvar(A_FV);
    let v = k.fvar(V_FV);
    let na = k.app(c.rneg, a);
    let u = c.act(k, a, v); // u := a • v
    let w = c.act(k, na, v); // w := (−a) • v
    let a_na = app2(k, c.radd, a, na);
    let ana_v = c.act(k, a_na, v);
    let zero_v = c.act(k, c.rzero, v);

    // step_a : (a + −a)•v ~ a•v + (−a)•v
    let uw = c.mplus(k, u, w);
    let step_a = t_app(k, as_, &[a, na, v]);
    // step_b : (a + −a)•v ~ 0•v ~ 0
    let neg_add_a = k.app(c.rneg_add, a); // R.equiv (a + −a) 0
    let refl_v = k.app(c.mrefl, v);
    let step_b1 = t_app(k, sc, &[a_na, c.rzero, v, v, neg_add_a, refl_v]);
    let step_b2 = {
        let t = k.const_(zero_smul, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, hm, v])
    };
    let step_b = c.mtr(k, ana_v, zero_v, c.me, step_b1, step_b2);
    // h2 : a•v + (−a)•v ~ 0
    let step_as = c.msy(k, ana_v, uw, step_a);
    let h2 = c.mtr(k, uw, ana_v, c.me, step_as, step_b);
    // h1 : (−a)•v + a•v ~ 0, via M.comm
    let wu = c.mplus(k, w, u);
    let comm_wu = t_app(k, c.mcomm, &[w, u]);
    let h1 = c.mtr(k, wu, uw, c.me, comm_wu, h2);
    // inv_unique G u w (inv u) h1 (M.invR u) : equiv w (inv u)
    let inv_u = k.app(c.minv, u);
    let inv_r_u = k.app(c.minv_r, u);
    let g = {
        let tg = k.const_(to_group, vec![]);
        k.app(tg, c.m)
    };
    let proof = {
        let t = k.const_(inv_unique, vec![]);
        t_app(k, t, &[g, u, w, inv_u, h1, inv_r_u])
    };

    let value = lam_over(k, V_FV, c.mc, proof);
    let value = lam_over(k, A_FV, c.rc, value);
    let value = lam_over(k, HM_FV, hyp_ty, value);
    let value = c.close_lam(k, value);

    let concl = c.meqv(k, w, inv_u);
    let ty = pi_over(k, V_FV, c.mc, concl);
    let ty = pi_over(k, A_FV, c.rc, ty);
    let ty = pi_over(k, HM_FV, hyp_ty, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(ns, "neg_smul");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// The two instances.
// ---------------------------------------------------------------------------

/// `AlgS.Module.selfModule : forall (R : AlgS.CommRing),
/// IsModule R (AlgS.CommRing.toCommGroupS R) (AlgS.CommRing.mul R)` — **`R`
/// is a module over itself**, and all five axioms are a SELECTOR each:
/// `mulCongr`, `distribL`, `distribR`, `mulAssoc`, `mulOneL`.
fn declare_self_module(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    ax: AxiomNames,
    is_module: NameId,
    to_comm_group: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use idx::comm_ring::{DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC, MUL_CONGR, MUL_ONE_L};
    let ring_ty = k.const_(cr.ind, vec![]);
    let r = k.fvar(R_FV);
    let m = {
        let t = k.const_(to_comm_group, vec![]);
        k.app(t, r)
    };
    let smul = sel(k, cr, MUL, r);
    let fields = [
        sel(k, cr, MUL_CONGR, r),
        sel(k, cr, DISTRIB_L, r),
        sel(k, cr, DISTRIB_R, r),
        sel(k, cr, MUL_ASSOC, r),
        sel(k, cr, MUL_ONE_L, r),
    ];
    let value = and_chain(k, lg, ax, r, m, smul, &fields);
    let value = lam_over(k, R_FV, ring_ty, value);

    let ty = {
        let t = k.const_(is_module, vec![]);
        let body = t_app(k, t, &[r, m, smul]);
        pi_over(k, R_FV, ring_ty, body)
    };

    let name = k.name_str(ns, "selfModule");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// Assemble `And.intro`s over the five axiom propositions instantiated at
/// `(r, m, smul)`, with `fields` supplying each proof.
fn and_chain(
    k: &mut Kernel,
    lg: &LogicPrelude,
    ax: AxiomNames,
    r: ExprId,
    m: ExprId,
    smul: ExprId,
    fields: &[ExprId; 5],
) -> ExprId {
    let props: Vec<ExprId> = ax
        .in_order()
        .iter()
        .map(|n| {
            let t = k.const_(*n, vec![]);
            t_app(k, t, &[r, m, smul])
        })
        .collect();
    let and_c = k.const_(lg.and, vec![]);
    let mut tail_prop = props[4];
    let mut tail_val = fields[4];
    for i in (0..4).rev() {
        let and_intro = k.const_(lg.and_intro, vec![]);
        tail_val = t_app(k, and_intro, &[props[i], tail_prop, fields[i], tail_val]);
        tail_prop = app2(k, and_c, props[i], tail_prop);
    }
    tail_val
}

/// `AlgS.Module.polyModule : forall (R : AlgS.CommRing),
/// IsModule R (AlgS.Poly.commGroup R) (AlgS.Poly.smul R)` — **`R[X]` is an
/// `R`-module**, the free module of countable rank. Every one of the five
/// axioms is ONE application of `R`'s corresponding field at the coefficient
/// index; the pointwise `equiv` is what makes that legal.
#[allow(clippy::too_many_arguments)]
fn declare_poly_module(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    ax: AxiomNames,
    is_module: NameId,
    poly_comm_group: NameId,
    poly_smul: NameId,
    poly_equiv: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use idx::comm_ring::{CARRIER, DISTRIB_L, DISTRIB_R, EQUIV, MUL_ASSOC, MUL_CONGR, MUL_ONE_L};
    let ring_ty = k.const_(cr.ind, vec![]);
    let r = k.fvar(R_FV);
    let rc = sel(k, cr, CARRIER, r);
    let req = sel(k, cr, EQUIV, r);
    let rmul_congr = sel(k, cr, MUL_CONGR, r);
    let rdistrib_l = sel(k, cr, DISTRIB_L, r);
    let rdistrib_r = sel(k, cr, DISTRIB_R, r);
    let rmul_assoc = sel(k, cr, MUL_ASSOC, r);
    let rmul_one_l = sel(k, cr, MUL_ONE_L, r);

    let nat = k.const_(lg.nat, vec![]);
    let poly_ty = arrow(k, nat, rc);
    let m = {
        let t = k.const_(poly_comm_group, vec![]);
        k.app(t, r)
    };
    let smul = {
        let t = k.const_(poly_smul, vec![]);
        k.app(t, r)
    };
    let peq = |k: &mut Kernel, p: ExprId, q: ExprId| {
        let t = k.const_(poly_equiv, vec![]);
        let t = k.app(t, r);
        app2(k, t, p, q)
    };

    // 1. smulCongrP: fun a a' p p' ha hp n => R.mulCongr a a' (p n) (p' n) (ha) (hp n)
    let f_congr = {
        let a = k.fvar(A_FV);
        let ap = k.fvar(AP_FV);
        let p = k.fvar(V_FV);
        let pp = k.fvar(VP_FV);
        let hyp1 = app2(k, req, a, ap);
        let hyp2 = peq(k, p, pp);
        let ha = k.fvar(H1_FV);
        let hp = k.fvar(H2_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let ppn = k.app(pp, n);
        let hpn = k.app(hp, n);
        let body = t_app(k, rmul_congr, &[a, ap, pn, ppn, ha, hpn]);
        let body = lam_over(k, N_FV, nat, body);
        let body = lam_over(k, H2_FV, hyp2, body);
        let body = lam_over(k, H1_FV, hyp1, body);
        let body = lam_over(k, VP_FV, poly_ty, body);
        let body = lam_over(k, V_FV, poly_ty, body);
        let body = lam_over(k, AP_FV, rc, body);
        lam_over(k, A_FV, rc, body)
    };
    // 2. smulAddP: fun a p q n => R.distribL a (p n) (q n)
    let f_smul_add = {
        let a = k.fvar(A_FV);
        let p = k.fvar(V_FV);
        let q = k.fvar(W_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let body = t_app(k, rdistrib_l, &[a, pn, qn]);
        let body = lam_over(k, N_FV, nat, body);
        let body = lam_over(k, W_FV, poly_ty, body);
        let body = lam_over(k, V_FV, poly_ty, body);
        lam_over(k, A_FV, rc, body)
    };
    // 3. addSmulP: fun a b p n => R.distribR a b (p n)
    let f_add_smul = {
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let p = k.fvar(V_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = t_app(k, rdistrib_r, &[a, b, pn]);
        let body = lam_over(k, N_FV, nat, body);
        let body = lam_over(k, V_FV, poly_ty, body);
        let body = lam_over(k, B_FV, rc, body);
        lam_over(k, A_FV, rc, body)
    };
    // 4. mulSmulP: fun a b p n => R.mulAssoc a b (p n)
    let f_mul_smul = {
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let p = k.fvar(V_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = t_app(k, rmul_assoc, &[a, b, pn]);
        let body = lam_over(k, N_FV, nat, body);
        let body = lam_over(k, V_FV, poly_ty, body);
        let body = lam_over(k, B_FV, rc, body);
        lam_over(k, A_FV, rc, body)
    };
    // 5. oneSmulP: fun p n => R.mulOneL (p n)
    let f_one_smul = {
        let p = k.fvar(V_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = k.app(rmul_one_l, pn);
        let body = lam_over(k, N_FV, nat, body);
        lam_over(k, V_FV, poly_ty, body)
    };

    let fields = [f_congr, f_smul_add, f_add_smul, f_mul_smul, f_one_smul];
    let value = and_chain(k, lg, ax, r, m, smul, &fields);
    let value = lam_over(k, R_FV, ring_ty, value);

    let ty = {
        let t = k.const_(is_module, vec![]);
        let body = t_app(k, t, &[r, m, smul]);
        pi_over(k, R_FV, ring_ty, body)
    };

    let name = k.name_str(ns, "polyModule");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// Linear combinations, spanning, independence, bases.
// ---------------------------------------------------------------------------

/// `AlgS.Module.linComb R M smul c v n := Σ_{i<n} (c i) • (v i)`, by `Nat.rec`
/// on `n`: `linComb … zero ≡ M.e`,
/// `linComb … (succ j) ≡ M.op (linComb … j) (smul (c j) (v j))` — the same
/// exclusive-bound, fold-on-the-right convention `Nat.sumRange` uses.
fn declare_lin_comb(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let nat = k.const_(lg.nat, vec![]);
    let coeff_ty = arrow(k, nat, c.rc);
    let vec_ty = arrow(k, nat, c.mc);

    let coeff = k.fvar(C_FV);
    let vecs = k.fvar(VEC_FV);
    let motive = lam_over(k, SCRATCH_FV, nat, c.mc);
    let minor_succ = {
        let j = k.fvar(J_FV);
        let ih = k.fvar(IH_FV);
        let cj = k.app(coeff, j);
        let vj = k.app(vecs, j);
        let term = c.act(k, cj, vj);
        let body = c.mplus(k, ih, term);
        let body = lam_over(k, IH_FV, c.mc, body);
        lam_over(k, J_FV, nat, body)
    };
    let n = k.fvar(N_FV);
    let rec = k.const_(lg.nat_rec, vec![l1]);
    let body = t_app(k, rec, &[motive, c.me, minor_succ, n]);
    let value = lam_over(k, N_FV, nat, body);
    let value = lam_over(k, VEC_FV, vec_ty, value);
    let value = lam_over(k, C_FV, coeff_ty, value);
    let value = c.close_lam(k, value);

    let ty = {
        let inner = arrow(k, nat, c.mc);
        let inner = arrow(k, vec_ty, inner);
        let inner = arrow(k, coeff_ty, inner);
        c.close_pi(k, inner)
    };

    let name = k.name_str(ns, "linComb");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Module.coeffAgree R c d n` — `c` and `d` agree at every index below
/// `n`, by `Nat.rec` on `n` (`True` at zero, `And (agree j) (R.equiv (c j)
/// (d j))` at `succ j`). This exists because `Nat.lt` is not declared yet at
/// the `AlgS` build position.
fn declare_coeff_agree(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use idx::comm_ring::{CARRIER, EQUIV};
    let l0 = k.level_zero();
    // `Nat.rec`'s universe here is ONE, not zero: the recursion returns a
    // `Prop`-VALUED object, so its motive is `fun _ => Prop` whose codomain
    // is `Sort 1` (`Prop : Sort 1`). Passing `l0` -- the level of the thing
    // being built rather than of its motive -- is the one rejection this
    // file cost, and it surfaces as `TypeMismatch { expected: Sort 0 }`.
    let l1 = k.level_succ(l0);
    let ring_ty = k.const_(cr.ind, vec![]);
    let r = k.fvar(R_FV);
    let rc = sel(k, cr, CARRIER, r);
    let req = sel(k, cr, EQUIV, r);
    let nat = k.const_(lg.nat, vec![]);
    let coeff_ty = arrow(k, nat, rc);
    let prop = k.sort(l0);

    let cf = k.fvar(C_FV);
    let df = k.fvar(D_FV);
    let motive = lam_over(k, SCRATCH_FV, nat, prop);
    let minor_zero = k.const_(lg.true_, vec![]);
    let minor_succ = {
        let j = k.fvar(J_FV);
        let ih = k.fvar(IH_FV);
        let cj = k.app(cf, j);
        let dj = k.app(df, j);
        let step = app2(k, req, cj, dj);
        let and_c = k.const_(lg.and, vec![]);
        let body = app2(k, and_c, ih, step);
        let body = lam_over(k, IH_FV, prop, body);
        lam_over(k, J_FV, nat, body)
    };
    let n = k.fvar(N_FV);
    let rec = k.const_(lg.nat_rec, vec![l1]);
    let body = t_app(k, rec, &[motive, minor_zero, minor_succ, n]);
    let value = lam_over(k, N_FV, nat, body);
    let value = lam_over(k, D_FV, coeff_ty, value);
    let value = lam_over(k, C_FV, coeff_ty, value);
    let value = lam_over(k, R_FV, ring_ty, value);

    let ty = {
        let inner = arrow(k, nat, prop);
        let inner = arrow(k, coeff_ty, inner);
        let inner = arrow(k, coeff_ty, inner);
        pi_over(k, R_FV, ring_ty, inner)
    };

    let name = k.name_str(ns, "coeffAgree");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Module.spans R M smul v n := forall w, exists c,
/// M.equiv (linComb R M smul c v n) w`.
fn declare_spans(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    lin_comb: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let nat = k.const_(lg.nat, vec![]);
    let coeff_ty = arrow(k, nat, c.rc);
    let vec_ty = arrow(k, nat, c.mc);
    let prop = k.sort(l0);

    let vecs = k.fvar(VEC_FV);
    let n = k.fvar(N_FV);
    let w = k.fvar(W_FV);
    let coeff = k.fvar(C_FV);
    let lc = {
        let t = k.const_(lin_comb, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, coeff, vecs, n])
    };
    let inner = c.meqv(k, lc, w);
    let pred = lam_over(k, C_FV, coeff_ty, inner);
    let ex = k.const_(lg.exists_, vec![l1]);
    let body = t_app(k, ex, &[coeff_ty, pred]);
    let body = pi_over(k, W_FV, c.mc, body);
    let value = lam_over(k, N_FV, nat, body);
    let value = lam_over(k, VEC_FV, vec_ty, value);
    let value = c.close_lam(k, value);

    let ty = {
        let inner = arrow(k, nat, prop);
        let inner = arrow(k, vec_ty, inner);
        c.close_pi(k, inner)
    };

    let name = k.name_str(ns, "spans");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;
    Ok(name)
}

/// `AlgS.Module.linearIndependent R M smul v n := forall c d,
/// M.equiv (linComb … c v n) (linComb … d v n) -> coeffAgree R c d n` — the
/// coordinate map is injective below `n`. Over a ring with subtraction this
/// is the usual independence statement, and it avoids `Nat.lt`.
fn declare_linear_independent(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    lin_comb: NameId,
    coeff_agree: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let l0 = k.level_zero();
    let nat = k.const_(lg.nat, vec![]);
    let coeff_ty = arrow(k, nat, c.rc);
    let vec_ty = arrow(k, nat, c.mc);
    let prop = k.sort(l0);

    let vecs = k.fvar(VEC_FV);
    let n = k.fvar(N_FV);
    let cf = k.fvar(C_FV);
    let df = k.fvar(D_FV);
    let lc = {
        let t = k.const_(lin_comb, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, cf, vecs, n])
    };
    let ld = {
        let t = k.const_(lin_comb, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, df, vecs, n])
    };
    let hyp = c.meqv(k, lc, ld);
    let concl = {
        let t = k.const_(coeff_agree, vec![]);
        t_app(k, t, &[c.r, cf, df, n])
    };
    let body = pi_over(k, H1_FV, hyp, concl);
    let body = pi_over(k, D_FV, coeff_ty, body);
    let body = pi_over(k, C_FV, coeff_ty, body);
    let value = lam_over(k, N_FV, nat, body);
    let value = lam_over(k, VEC_FV, vec_ty, value);
    let value = c.close_lam(k, value);

    let ty = {
        let inner = arrow(k, nat, prop);
        let inner = arrow(k, vec_ty, inner);
        c.close_pi(k, inner)
    };

    let name = k.name_str(ns, "linearIndependent");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;
    Ok(name)
}

/// `AlgS.Module.isBasis R M smul v n := And (spans …) (linearIndependent …)`.
fn declare_is_basis(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    spans: NameId,
    lin_indep: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let l0 = k.level_zero();
    let nat = k.const_(lg.nat, vec![]);
    let vec_ty = arrow(k, nat, c.mc);
    let prop = k.sort(l0);

    let vecs = k.fvar(VEC_FV);
    let n = k.fvar(N_FV);
    let sp = {
        let t = k.const_(spans, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, vecs, n])
    };
    let li = {
        let t = k.const_(lin_indep, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, vecs, n])
    };
    let and_c = k.const_(lg.and, vec![]);
    let body = app2(k, and_c, sp, li);
    let value = lam_over(k, N_FV, nat, body);
    let value = lam_over(k, VEC_FV, vec_ty, value);
    let value = c.close_lam(k, value);

    let ty = {
        let inner = arrow(k, nat, prop);
        let inner = arrow(k, vec_ty, inner);
        c.close_pi(k, inner)
    };

    let name = k.name_str(ns, "isBasis");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(name)
}

/// `AlgS.Module.linComb_congr : forall R M smul, IsModule R M smul ->
/// forall c d v n, coeffAgree R c d n ->
/// M.equiv (linComb R M smul c v n) (linComb R M smul d v n)`.
///
/// `Nat.rec` on `n`. The base is `M.equivRefl M.e`; the successor step is one
/// `M.opCongr` whose two arguments are the induction hypothesis (applied to
/// `And.left` of the agreement) and the module's own `smulCongr` (applied to
/// `And.right`). **This is the easy half of independence**, and its converse
/// is exactly what `linearIndependent` asserts.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_lin_comb_congr(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    cg: &RecordNames,
    is_module: NameId,
    smul_congr_acc: NameId,
    lin_comb: NameId,
    coeff_agree: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let c = mctx(k, cr, cg);
    let l0 = k.level_zero();
    let nat = k.const_(lg.nat, vec![]);
    let coeff_ty = arrow(k, nat, c.rc);
    let vec_ty = arrow(k, nat, c.mc);

    let hyp_ty = {
        let t = k.const_(is_module, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul])
    };
    let hm = k.fvar(HM_FV);
    let sc = {
        let t = k.const_(smul_congr_acc, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, hm])
    };

    let cf = k.fvar(C_FV);
    let df = k.fvar(D_FV);
    let vecs = k.fvar(VEC_FV);

    let comb = |k: &mut Kernel, coeffs: ExprId, n: ExprId| {
        let t = k.const_(lin_comb, vec![]);
        t_app(k, t, &[c.r, c.m, c.smul, coeffs, vecs, n])
    };
    let agree = |k: &mut Kernel, n: ExprId| {
        let t = k.const_(coeff_agree, vec![]);
        t_app(k, t, &[c.r, cf, df, n])
    };
    let motive_body = |k: &mut Kernel, n: ExprId| {
        let hyp = agree(k, n);
        let lhs = comb(k, cf, n);
        let rhs = comb(k, df, n);
        let concl = c.meqv(k, lhs, rhs);
        pi_over(k, H1_FV, hyp, concl)
    };

    let motive = {
        let n = k.fvar(N_FV);
        let body = motive_body(k, n);
        lam_over(k, N_FV, nat, body)
    };
    let minor_zero = {
        let zero_n = k.const_(lg.nat_zero, vec![]);
        let hyp = agree(k, zero_n);
        let body = k.app(c.mrefl, c.me);
        lam_over(k, H1_FV, hyp, body)
    };
    let minor_succ = {
        let j = k.fvar(J_FV);
        let ih_ty = motive_body(k, j);
        let ih = k.fvar(IH_FV);
        let succ_c = k.const_(lg.nat_succ, vec![]);
        let sj = k.app(succ_c, j);
        let hyp_sj = agree(k, sj);
        let h = k.fvar(H2_FV);

        let prev = agree(k, j);
        let cj = k.app(cf, j);
        let dj = k.app(df, j);
        let step_prop = app2(k, c.req, cj, dj);
        let and_left = k.const_(lg.and_left, vec![]);
        let and_right = k.const_(lg.and_right, vec![]);
        let h_prev = t_app(k, and_left, &[prev, step_prop, h]);
        let h_step = t_app(k, and_right, &[prev, step_prop, h]);

        let lhs_prev = comb(k, cf, j);
        let rhs_prev = comb(k, df, j);
        let ih_applied = k.app(ih, h_prev);

        let vj = k.app(vecs, j);
        let refl_v = k.app(c.mrefl, vj);
        let term_l = c.act(k, cj, vj);
        let term_r = c.act(k, dj, vj);
        let term_congr = t_app(k, sc, &[cj, dj, vj, vj, h_step, refl_v]);

        let body = t_app(
            k,
            c.mop_congr,
            &[lhs_prev, rhs_prev, term_l, term_r, ih_applied, term_congr],
        );
        let body = lam_over(k, H2_FV, hyp_sj, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, J_FV, nat, body)
    };
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let proof = t_app(k, rec, &[motive, minor_zero, minor_succ]);

    let value = lam_over(k, VEC_FV, vec_ty, proof);
    let value = lam_over(k, D_FV, coeff_ty, value);
    let value = lam_over(k, C_FV, coeff_ty, value);
    let value = lam_over(k, HM_FV, hyp_ty, value);
    let value = c.close_lam(k, value);

    let concl = {
        let n = k.fvar(N_FV);
        let body = motive_body(k, n);
        pi_over(k, N_FV, nat, body)
    };
    let ty = pi_over(k, VEC_FV, vec_ty, concl);
    let ty = pi_over(k, D_FV, coeff_ty, ty);
    let ty = pi_over(k, C_FV, coeff_ty, ty);
    let ty = pi_over(k, HM_FV, hyp_ty, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(ns, "linComb_congr");
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
pub struct ModuleNames {
    pub idem_eq_e: NameId,
    pub smul_congr_p: NameId,
    pub smul_add_p: NameId,
    pub add_smul_p: NameId,
    pub mul_smul_p: NameId,
    pub one_smul_p: NameId,
    pub is_module: NameId,
    pub smul_congr: NameId,
    pub smul_add: NameId,
    pub add_smul: NameId,
    pub mul_smul: NameId,
    pub one_smul: NameId,
    pub smul_zero: NameId,
    pub zero_smul: NameId,
    pub neg_smul: NameId,
    pub self_module: NameId,
    pub poly_module: NameId,
    pub lin_comb: NameId,
    pub coeff_agree: NameId,
    pub spans: NameId,
    pub linear_independent: NameId,
    pub is_basis: NameId,
    pub lin_comb_congr: NameId,
}

/// `#[cfg(test)]` for the same reason `PolyNames::all` is: these names are
/// deliberately not threaded into `NatPrelude`.
#[cfg(test)]
impl ModuleNames {
    #[must_use]
    pub fn all(&self) -> [NameId; 23] {
        [
            self.idem_eq_e,
            self.smul_congr_p,
            self.smul_add_p,
            self.add_smul_p,
            self.mul_smul_p,
            self.one_smul_p,
            self.is_module,
            self.smul_congr,
            self.smul_add,
            self.add_smul,
            self.mul_smul,
            self.one_smul,
            self.smul_zero,
            self.zero_smul,
            self.neg_smul,
            self.self_module,
            self.poly_module,
            self.lin_comb,
            self.coeff_agree,
            self.spans,
            self.linear_independent,
            self.is_basis,
            self.lin_comb_congr,
        ]
    }
}

/// What this module needs from `structures_setoid`'s extras and from
/// `polynomial_setoid`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleDeps {
    pub add_left_cancel: NameId,
    pub inv_unique: NameId,
    pub comm_ring_to_comm_group_s: NameId,
    pub comm_group_to_group_s: NameId,
    pub poly_comm_group: NameId,
    pub poly_smul: NameId,
    pub poly_equiv: NameId,
}

/// Declare `AlgS.idem_eq_e` and the whole `AlgS.Module.*` namespace.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means
/// [`Kernel::add_declaration`] **refused** a proof term.
pub(crate) fn declare_module_setoid(
    k: &mut Kernel,
    lg: &LogicPrelude,
    comm_ring: &RecordNames,
    comm_group: &RecordNames,
    group: &RecordNames,
    deps: ModuleDeps,
    algs_p: NameId,
) -> Result<ModuleNames, KernelError> {
    let ns = k.name_str(algs_p, "Module");

    let idem_eq_e = declare_idem_eq_e(k, group, deps.add_left_cancel, algs_p)?;

    let ax = AxiomNames {
        smul_congr_p: declare_axiom_pred(
            k,
            comm_ring,
            comm_group,
            ns,
            "smulCongrP",
            &smul_congr_stmt,
        )?,
        smul_add_p: declare_axiom_pred(k, comm_ring, comm_group, ns, "smulAddP", &smul_add_stmt)?,
        add_smul_p: declare_axiom_pred(k, comm_ring, comm_group, ns, "addSmulP", &add_smul_stmt)?,
        mul_smul_p: declare_axiom_pred(k, comm_ring, comm_group, ns, "mulSmulP", &mul_smul_stmt)?,
        one_smul_p: declare_axiom_pred(k, comm_ring, comm_group, ns, "oneSmulP", &one_smul_stmt)?,
    };
    let is_module = declare_is_module(k, lg, comm_ring, comm_group, ax, ns)?;

    let suffixes = ["smulCongr", "smulAdd", "addSmul", "mulSmul", "oneSmul"];
    let mut accs = Vec::with_capacity(5);
    for (i, suffix) in suffixes.iter().enumerate() {
        accs.push(declare_accessor(
            k, lg, comm_ring, comm_group, is_module, ax, i, suffix, ns,
        )?);
    }
    let acc = AccessorNames {
        smul_congr: accs[0],
        smul_add: accs[1],
        add_smul: accs[2],
        mul_smul: accs[3],
        one_smul: accs[4],
    };

    let smul_zero = declare_smul_zero(
        k,
        comm_ring,
        comm_group,
        is_module,
        acc,
        accs[1],
        idem_eq_e,
        deps.comm_group_to_group_s,
        ns,
    )?;
    let zero_smul = declare_zero_smul(
        k,
        comm_ring,
        comm_group,
        is_module,
        acc,
        idem_eq_e,
        deps.comm_group_to_group_s,
        ns,
    )?;
    let neg_smul = declare_neg_smul(
        k,
        comm_ring,
        comm_group,
        is_module,
        acc,
        zero_smul,
        deps.inv_unique,
        deps.comm_group_to_group_s,
        ns,
    )?;

    let self_module = declare_self_module(
        k,
        lg,
        comm_ring,
        ax,
        is_module,
        deps.comm_ring_to_comm_group_s,
        ns,
    )?;
    let poly_module = declare_poly_module(
        k,
        lg,
        comm_ring,
        ax,
        is_module,
        deps.poly_comm_group,
        deps.poly_smul,
        deps.poly_equiv,
        ns,
    )?;

    let lin_comb = declare_lin_comb(k, lg, comm_ring, comm_group, ns)?;
    let coeff_agree = declare_coeff_agree(k, lg, comm_ring, ns)?;
    let spans = declare_spans(k, lg, comm_ring, comm_group, lin_comb, ns)?;
    let linear_independent =
        declare_linear_independent(k, lg, comm_ring, comm_group, lin_comb, coeff_agree, ns)?;
    let is_basis = declare_is_basis(k, lg, comm_ring, comm_group, spans, linear_independent, ns)?;
    let lin_comb_congr = declare_lin_comb_congr(
        k,
        lg,
        comm_ring,
        comm_group,
        is_module,
        acc.smul_congr,
        lin_comb,
        coeff_agree,
        ns,
    )?;

    Ok(ModuleNames {
        idem_eq_e,
        smul_congr_p: ax.smul_congr_p,
        smul_add_p: ax.smul_add_p,
        add_smul_p: ax.add_smul_p,
        mul_smul_p: ax.mul_smul_p,
        one_smul_p: ax.one_smul_p,
        is_module,
        smul_congr: accs[0],
        smul_add: accs[1],
        add_smul: accs[2],
        mul_smul: accs[3],
        one_smul: accs[4],
        smul_zero,
        zero_smul,
        neg_smul,
        self_module,
        poly_module,
        lin_comb,
        coeff_agree,
        spans,
        linear_independent,
        is_basis,
        lin_comb_congr,
    })
}

// ---------------------------------------------------------------------------
// Tests. Every assertion reads the KERNEL.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod module_setoid_tests {
    use super::*;
    use crate::build_logic_prelude;
    use crate::nat_prelude::polynomial_setoid::{PolyNames, declare_poly_setoid};
    use crate::nat_prelude::structures as algeq;
    use crate::nat_prelude::structures_setoid::{
        StructuresSExtraNames, StructuresSNames, StructuresSRecordNames, declare_structures_s_all,
        declare_structures_s_extra, intern_structures_s_names,
    };

    struct Fixture {
        lg: LogicPrelude,
        st: StructuresSRecordNames,
        p: StructuresSNames,
        extra: StructuresSExtraNames,
        poly: PolyNames,
        m: ModuleNames,
    }

    fn build(k: &mut Kernel) -> Fixture {
        let lg = build_logic_prelude(k).expect("logic prelude must build");
        let alg_p = algeq::intern_structures_names(k);
        let alg_st = algeq::declare_structures_all(k, &alg_p, &lg).expect("Alg spine builds");
        let p = intern_structures_s_names(k);
        let st = declare_structures_s_all(k, &p, &lg).expect("AlgS spine builds");
        let extra = declare_structures_s_extra(k, &lg, &p, &st, &alg_p, &alg_st)
            .expect("AlgS extras must admit");
        let poly = declare_poly_setoid(k, &lg, &st.comm_ring, &st.comm_group, p.algs)
            .expect("AlgS.Poly must admit");
        let deps = ModuleDeps {
            add_left_cancel: extra.add_left_cancel,
            inv_unique: extra.inv_unique,
            comm_ring_to_comm_group_s: extra.comm_ring_to_comm_group_s,
            comm_group_to_group_s: extra.comm_group_to_group_s,
            poly_comm_group: poly.comm_group,
            poly_smul: poly.ops.smul,
            poly_equiv: poly.ops.equiv,
        };
        let m = declare_module_setoid(
            k,
            &lg,
            &st.comm_ring,
            &st.comm_group,
            &st.group,
            deps,
            p.algs,
        )
        .expect("AlgS.Module over an abstract AlgS.CommRing must admit");
        Fixture {
            lg,
            st,
            p,
            extra,
            poly,
            m,
        }
    }

    #[test]
    fn the_module_layer_admits_by_the_setoid_route() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.m.all() {
            assert!(
                k.environment().get(name).is_some(),
                "declaration missing from the environment"
            );
        }
    }

    /// **The headline claim**, read from `Kernel::axiom_footprint`.
    #[test]
    fn the_module_layer_is_axiom_free() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.m.all() {
            let footprint = k.axiom_footprint(name);
            assert!(
                footprint.is_empty(),
                "axiom footprint must be empty, got {} entries",
                footprint.len()
            );
        }
    }

    /// The two instances and the three generic theorems are `Theorem`s, so
    /// the kernel checked their proof terms against the `IsModule`
    /// proposition -- there is no way to pass this with a stub.
    #[test]
    fn the_instances_and_generic_theorems_are_checked_theorems() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in [
            f.m.self_module,
            f.m.poly_module,
            f.m.smul_zero,
            f.m.zero_smul,
            f.m.neg_smul,
            f.m.lin_comb_congr,
            f.m.idem_eq_e,
        ] {
            let d = k
                .environment()
                .get(name)
                .expect("theorem must exist")
                .clone();
            assert!(
                matches!(d, Declaration::Theorem { .. }),
                "must be a checked Theorem"
            );
        }
    }

    /// Every declaration's type renders and mentions the abstract spine.
    /// Prints them so a referee can read the statements out of the suite.
    #[test]
    fn the_module_layer_types_render() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.m.all() {
            let decl = k
                .environment()
                .get(name)
                .expect("declaration must exist")
                .clone();
            let ty = match &decl {
                Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
                _ => panic!("unexpected declaration kind"),
            };
            let rendered = k.render_lean(ty);
            println!("decl {name:?} :\n  {rendered}\n");
            assert!(
                rendered.contains("AlgS."),
                "every declaration must be stated over the abstract AlgS \
                 spine, got: {rendered}"
            );
        }
    }

    /// **Evaluation test for `AlgS.Module.linComb`.** With `R`, `M`, `smul`,
    /// `c` and `v` free, the definition must reduce at concrete bounds to the
    /// hand-written fold, and NOT to the fold with the last two terms
    /// swapped (a change of two subterms) or to a left-open sum (an
    /// off-by-one).
    #[test]
    fn lin_comb_folds_the_first_n_terms_on_the_right() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let c = mctx(&mut k, &f.st.comm_ring, &f.st.comm_group);
        let nat = k.const_(f.lg.nat, vec![]);
        let coeff_ty = arrow(&mut k, nat, c.rc);
        let vec_ty = arrow(&mut k, nat, c.mc);
        let cf = k.fvar(C_FV);
        let vf = k.fvar(VEC_FV);
        let _ = (coeff_ty, vec_ty);

        let numeral = |k: &mut Kernel, n: usize| {
            let mut e = k.const_(f.lg.nat_zero, vec![]);
            for _ in 0..n {
                let s = k.const_(f.lg.nat_succ, vec![]);
                e = k.app(s, e);
            }
            e
        };
        let lc = |k: &mut Kernel, n: usize| {
            let t = k.const_(f.m.lin_comb, vec![]);
            let nn = numeral(k, n);
            t_app(k, t, &[c.r, c.m, c.smul, cf, vf, nn])
        };
        let term = |k: &mut Kernel, i: usize| {
            let ii = numeral(k, i);
            let ci = k.app(cf, ii);
            let vi = k.app(vf, ii);
            c.act(k, ci, vi)
        };

        // n = 0 is the empty sum.
        {
            let lhs = lc(&mut k, 0);
            assert!(k.def_eq(lhs, c.me), "linComb .. 0 must be M.e");
            let t0 = term(&mut k, 0);
            assert!(
                !k.def_eq(lhs, t0),
                "linComb .. 0 must NOT already include the index-0 term"
            );
        }
        // n = 1 : M.op M.e (c 0 . v 0).
        {
            let lhs = lc(&mut k, 1);
            let t0 = term(&mut k, 0);
            let rhs = c.mplus(&mut k, c.me, t0);
            assert!(k.def_eq(lhs, rhs), "linComb .. 1 must be e + c0.v0");
            assert!(
                !k.def_eq(lhs, t0),
                "linComb .. 1 must keep the identity summand -- the fold is \
                 exclusive-bound and starts from M.e"
            );
        }
        // n = 2 : M.op (M.op M.e (c 0 . v 0)) (c 1 . v 1) -- left-nested.
        {
            let lhs = lc(&mut k, 2);
            let t0 = term(&mut k, 0);
            let t1 = term(&mut k, 1);
            let head = c.mplus(&mut k, c.me, t0);
            let rhs = c.mplus(&mut k, head, t1);
            assert!(
                k.def_eq(lhs, rhs),
                "linComb .. 2 must be (e + c0.v0) + c1.v1"
            );
            let swapped = {
                let head2 = c.mplus(&mut k, c.me, t1);
                c.mplus(&mut k, head2, t0)
            };
            assert!(
                !k.def_eq(lhs, swapped),
                "linComb .. 2 must NOT be (e + c1.v1) + c0.v0 -- the group is \
                 abstract, so the summation order is observable"
            );
        }
    }

    /// **Evaluation test for `AlgS.Module.coeffAgree`**: `True` at bound
    /// zero, and one `And` per index after, with the negative twin being the
    /// bound one lower.
    #[test]
    fn coeff_agree_accumulates_one_conjunct_per_index() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let c = mctx(&mut k, &f.st.comm_ring, &f.st.comm_group);
        let cf = k.fvar(C_FV);
        let df = k.fvar(D_FV);

        let numeral = |k: &mut Kernel, n: usize| {
            let mut e = k.const_(f.lg.nat_zero, vec![]);
            for _ in 0..n {
                let s = k.const_(f.lg.nat_succ, vec![]);
                e = k.app(s, e);
            }
            e
        };
        let agree = |k: &mut Kernel, n: usize| {
            let t = k.const_(f.m.coeff_agree, vec![]);
            let nn = numeral(k, n);
            t_app(k, t, &[c.r, cf, df, nn])
        };
        let at = |k: &mut Kernel, i: usize| {
            let ii = numeral(k, i);
            let ci = k.app(cf, ii);
            let di = k.app(df, ii);
            app2(k, c.req, ci, di)
        };

        let true_c = k.const_(f.lg.true_, vec![]);
        let a0 = agree(&mut k, 0);
        assert!(k.def_eq(a0, true_c), "coeffAgree .. 0 must be True");

        let a1 = agree(&mut k, 1);
        let e0 = at(&mut k, 0);
        let and_c = k.const_(f.lg.and, vec![]);
        let want1 = app2(&mut k, and_c, true_c, e0);
        assert!(
            k.def_eq(a1, want1),
            "coeffAgree .. 1 must be And True (c0~d0)"
        );
        assert!(
            !k.def_eq(a1, true_c),
            "coeffAgree .. 1 must NOT collapse to the bound-zero statement"
        );

        let a2 = agree(&mut k, 2);
        let e1 = at(&mut k, 1);
        let and_c2 = k.const_(f.lg.and, vec![]);
        let want2 = app2(&mut k, and_c2, want1, e1);
        assert!(
            k.def_eq(a2, want2),
            "coeffAgree .. 2 must add the index-1 conjunct"
        );
        assert!(
            !k.def_eq(a2, want1),
            "coeffAgree .. 2 must NOT equal the bound-one statement"
        );
    }

    /// **Negative control for the instances.** `AlgS.Module.polyModule`'s
    /// own proof term is re-declared against the `IsModule` statement for the
    /// SELF module (`R` over itself), a change of exactly the `M` and `smul`
    /// arguments. The kernel must refuse it. The positive twin is the
    /// re-declaration against its own statement, which must be accepted --
    /// otherwise the refusal would only show that re-declaration is broken.
    #[test]
    fn the_poly_module_proof_does_not_check_against_the_self_module_statement() {
        use idx::comm_ring::MUL;
        let mut k = Kernel::new();
        let f = build(&mut k);
        let ring_ty = k.const_(f.st.comm_ring.ind, vec![]);
        let r = k.fvar(R_FV);

        let value = match k
            .environment()
            .get(f.m.poly_module)
            .expect("polyModule must exist")
        {
            Declaration::Theorem { value, .. } => *value,
            other => panic!("expected a Theorem, got {other:?}"),
        };

        let stmt = |k: &mut Kernel, poly: bool| {
            let (m, smul) = if poly {
                let cg = k.const_(f.poly.comm_group, vec![]);
                let sm = k.const_(f.poly.ops.smul, vec![]);
                (k.app(cg, r), k.app(sm, r))
            } else {
                let cg = k.const_(f.extra.comm_ring_to_comm_group_s, vec![]);
                (k.app(cg, r), sel(k, &f.st.comm_ring, MUL, r))
            };
            let t = k.const_(f.m.is_module, vec![]);
            let body = t_app(k, t, &[r, m, smul]);
            pi_over(k, R_FV, ring_ty, body)
        };

        // Positive twin.
        let own = stmt(&mut k, true);
        let own_name = k.name_str(f.p.algs, "polyModuleRestatedControl");
        assert!(
            k.add_declaration(Declaration::Theorem {
                name: own_name,
                uparams: vec![],
                ty: own,
                value,
            })
            .is_ok(),
            "re-declaring polyModule's proof against its own statement must \
             admit -- otherwise the refusal below proves nothing"
        );

        // The mutant: the same proof against the self-module statement.
        let other = stmt(&mut k, false);
        let other_name = k.name_str(f.p.algs, "polyModuleAtSelfModule");
        assert!(
            k.add_declaration(Declaration::Theorem {
                name: other_name,
                uparams: vec![],
                ty: other,
                value,
            })
            .is_err(),
            "R[X]'s module proof must NOT check against R-over-itself: the \
             two differ in the group and the action, and the coefficientwise \
             proofs are specific to the polynomial carrier"
        );
    }

    /// **Negative control for `AlgS.idem_eq_e`.** Its proof is re-declared
    /// against the statement with the conclusion's two sides swapped
    /// (`G.equiv G.e x` instead of `G.equiv x G.e`) -- one subterm exchange
    /// -- and must be refused, with the honest restatement admitted in the
    /// same test.
    #[test]
    fn idem_eq_e_is_rejected_with_the_conclusion_reversed() {
        use idx::group::{CARRIER, E, EQUIV, OP};
        let mut k = Kernel::new();
        let f = build(&mut k);
        let group = &f.st.group;
        let group_ty = k.const_(group.ind, vec![]);
        let g = k.fvar(G_FV);
        let carrier = sel(&mut k, group, CARRIER, g);
        let equiv = sel(&mut k, group, EQUIV, g);
        let op = sel(&mut k, group, OP, g);
        let e = sel(&mut k, group, E, g);
        let x = k.fvar(X_FV);
        let xx = app2(&mut k, op, x, x);
        let hyp = app2(&mut k, equiv, x, xx);

        let value = match k
            .environment()
            .get(f.m.idem_eq_e)
            .expect("idem_eq_e must exist")
        {
            Declaration::Theorem { value, .. } => *value,
            other => panic!("expected a Theorem, got {other:?}"),
        };

        let close = |k: &mut Kernel, concl: ExprId| {
            let t = pi_over(k, H1_FV, hyp, concl);
            let t = pi_over(k, X_FV, carrier, t);
            pi_over(k, G_FV, group_ty, t)
        };
        let honest = {
            let concl = app2(&mut k, equiv, x, e);
            close(&mut k, concl)
        };
        let reversed = {
            let concl = app2(&mut k, equiv, e, x);
            close(&mut k, concl)
        };

        let ok_name = k.name_str(f.p.algs, "idemEqERestatedControl");
        assert!(
            k.add_declaration(Declaration::Theorem {
                name: ok_name,
                uparams: vec![],
                ty: honest,
                value,
            })
            .is_ok(),
            "the honest restatement must admit"
        );
        let bad_name = k.name_str(f.p.algs, "idemEqEReversed");
        assert!(
            k.add_declaration(Declaration::Theorem {
                name: bad_name,
                uparams: vec![],
                ty: reversed,
                value,
            })
            .is_err(),
            "the proof concludes `equiv x e`; `equiv e x` is a different \
             proposition over an abstract setoid and must be refused"
        );
    }
}
