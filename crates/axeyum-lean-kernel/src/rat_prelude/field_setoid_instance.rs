//! ADR-1627: **ℚ as an `AlgS.Field`** — the trivial case, and the one that
//! shows what "trivial" costs.
//!
//! `ℚ` has decidable equality, so its apartness is just `Not (Eq Rat a b)` and
//! the whole apartness layer is `Rat.lt_trichotomy` plus two `Eq.rec`
//! transports. **The setoid cost is zero**: `AlgS.CommRing.ofAlg
//! Rat.commRing` supplies all 23 ring fields with `equiv := @Eq Rat`, and the
//! six field-specific arguments are proved here.
//!
//! | name | what it is |
//! |---|---|
//! | `Rat.ne_of_lt` | `lt a b → Not (Eq Rat a b)` — the transport both branches need |
//! | `Rat.apart` | `fun a b => Not (Eq Rat a b)` |
//! | `Rat.apart_symm` | |
//! | `Rat.apart_cotrans` | the one place decidability is used |
//! | `Rat.apart_compat` | `Eq a b → apart a b → False`, i.e. `fun e h => h e` |
//! | `Rat.mulInvEx` | `Exists.intro` at `Rat.inv a`, closed by `Rat.mul_inv_cancel_of_ne_zero` |
//! | `Rat.fieldS` | `AlgS.Field.ofCommRing (AlgS.CommRing.ofAlg Rat.commRing) …` |
//! | `Rat.fieldS_isTight` | `AlgS.Field.IsTight Rat.fieldS` — **ℚ's apartness IS tight** |
//!
//! `fieldS_isTight` is the half of the tightness story `CReal` cannot supply
//! (see `nat_prelude::field_setoid`'s module doc for why tightness is a
//! predicate rather than a record field). It is the reason that predicate is
//! not vacuous.

use super::RatPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::structures::{app2, arrow, lam_over, pi_over};

const A_FV: u64 = 26_000;
const B_FV: u64 = 26_001;
const C_FV: u64 = 26_002;
const X_FV: u64 = 26_003;
const H1_FV: u64 = 26_010;
const H2_FV: u64 = 26_011;
const H3_FV: u64 = 26_012;
const SCRATCH_FV: u64 = 26_020;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

/// Everything this module declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RatFieldSNames {
    pub ne_of_lt: NameId,
    pub apart: NameId,
    pub apart_symm: NameId,
    pub apart_cotrans: NameId,
    pub apart_compat: NameId,
    pub mul_inv_ex: NameId,
    pub field_s: NameId,
    pub field_s_is_tight: NameId,
}

/// The `AlgS.Field` names, re-derived from the interned `AlgS` root rather
/// than threaded through `NatPrelude` — `name_str` is interned, so these are
/// the same `NameId`s `nat_prelude::field_setoid` produced.
struct AlgsField {
    of_comm_ring: NameId,
    is_tight: NameId,
    ind: NameId,
}

fn algs_field(k: &mut Kernel) -> AlgsField {
    let anon = k.anon();
    let algs = k.name_str(anon, "AlgS");
    let field = k.name_str(algs, "Field");
    AlgsField {
        of_comm_ring: k.name_str(field, "ofCommRing"),
        is_tight: k.name_str(field, "IsTight"),
        ind: field,
    }
}

/// The `ℚ` constants this module builds terms out of.
struct Q {
    rat: ExprId,
    zero: ExprId,
    one: ExprId,
    mul: ExprId,
    inv: ExprId,
    lt: ExprId,
    /// `Eq.{1} Rat`, partially applied — the `equiv` of `ofAlg Rat.commRing`.
    eq_rat: ExprId,
    false_: ExprId,
    lvl1: crate::level::LevelId,
}

fn qctx(k: &mut Kernel, p: &RatPrelude) -> Q {
    let lg = p.int.nat.logic;
    let l0 = k.level_zero();
    let lvl1 = k.level_succ(l0);
    let rat = k.const_(p.int.rat, vec![]);
    let eq_c = k.const_(lg.eq, vec![lvl1]);
    Q {
        rat,
        zero: k.const_(p.zero, vec![]),
        one: k.const_(p.one, vec![]),
        mul: k.const_(p.int.rat_mul, vec![]),
        inv: k.const_(p.inv, vec![]),
        lt: k.const_(p.lt, vec![]),
        eq_rat: k.app(eq_c, rat),
        false_: k.const_(lg.false_, vec![]),
        lvl1,
    }
}

impl Q {
    fn eq(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.eq_rat, a, b)
    }
    /// `Eq a b -> False`, the unfolded `Not (Eq a b)` the field spec's
    /// `apart` slot beta-reduces to.
    fn ne(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        let e = self.eq(k, a, b);
        arrow(k, e, self.false_)
    }
    fn lt_of(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.lt, a, b)
    }
}

/// `Rat.ne_of_lt : forall a b, Rat.lt a b -> Eq Rat a b -> False`.
///
/// The transport every branch of cotransitivity and of tightness needs:
/// `Eq.rec` with motive `fun x _ => Not (lt a x)` carries `Rat.lt_irrefl a`
/// from `x := a` to `x := b`.
fn declare_ne_of_lt(k: &mut Kernel, p: &RatPrelude) -> Result<NameId, KernelError> {
    let lg = p.int.nat.logic;
    let q = qctx(k, p);
    let l0 = k.level_zero();

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let hlt_ty = q.lt_of(k, a, b);
    let hlt = k.fvar(H1_FV);
    let heq_ty = q.eq(k, a, b);
    let heq = k.fvar(H2_FV);

    // `motive := fun (x : Rat) (_ : Eq Rat a x) => (lt a x -> False)`.
    let motive = {
        let x = k.fvar(X_FV);
        let ax = q.lt_of(k, a, x);
        let body = arrow(k, ax, q.false_);
        let eq_ax = q.eq(k, a, x);
        let inner = lam_over(k, SCRATCH_FV, eq_ax, body);
        lam_over(k, X_FV, q.rat, inner)
    };
    let refl_case = {
        let t = k.const_(p.lt_irrefl, vec![]);
        k.app(t, a)
    };
    let rec = k.const_(lg.eq_rec, vec![l0, q.lvl1]);
    let transported = t_app(k, rec, &[q.rat, a, motive, refl_case, b, heq]);
    let proof = k.app(transported, hlt);

    let value = lam_over(k, H2_FV, heq_ty, proof);
    let value = lam_over(k, H1_FV, hlt_ty, value);
    let value = lam_over(k, B_FV, q.rat, value);
    let value = lam_over(k, A_FV, q.rat, value);

    let ty = arrow(k, heq_ty, q.false_);
    let ty = arrow(k, hlt_ty, ty);
    let ty = pi_over(k, B_FV, q.rat, ty);
    let ty = pi_over(k, A_FV, q.rat, ty);

    let name = k.name_str(p.int.rat, "ne_of_lt");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `Rat.apart : Rat -> Rat -> Prop := fun a b => Eq Rat a b -> False`.
fn declare_apart(k: &mut Kernel, p: &RatPrelude) -> Result<NameId, KernelError> {
    let q = qctx(k, p);
    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let body = q.ne(k, a, b);
    let value = lam_over(k, B_FV, q.rat, body);
    let value = lam_over(k, A_FV, q.rat, value);
    let ty = {
        let inner = arrow(k, q.rat, prop);
        arrow(k, q.rat, inner)
    };
    let name = k.name_str(p.int.rat, "apart");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `Rat.apart_symm : forall a b, Rat.apart a b -> Rat.apart b a`.
fn declare_apart_symm(k: &mut Kernel, p: &RatPrelude, apart: NameId) -> Result<NameId, KernelError> {
    let lg = p.int.nat.logic;
    let q = qctx(k, p);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let hyp_ty = q.ne(k, a, b);
    let h = k.fvar(H1_FV);
    let e_ty = q.eq(k, b, a);
    let e = k.fvar(H2_FV);
    let symm = k.const_(lg.eq_symm, vec![q.lvl1]);
    let flipped = t_app(k, symm, &[q.rat, b, a, e]);
    let body = k.app(h, flipped);
    let value = lam_over(k, H2_FV, e_ty, body);
    let value = lam_over(k, H1_FV, hyp_ty, value);
    let value = lam_over(k, B_FV, q.rat, value);
    let value = lam_over(k, A_FV, q.rat, value);

    let ap = k.const_(apart, vec![]);
    let lhs = app2(k, ap, a, b);
    let rhs = app2(k, ap, b, a);
    let ty = arrow(k, lhs, rhs);
    let ty = pi_over(k, B_FV, q.rat, ty);
    let ty = pi_over(k, A_FV, q.rat, ty);

    let name = k.name_str(p.int.rat, "apart_symm");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `Rat.apart_cotrans : forall a b, Rat.apart a b -> forall c,
/// Or (Rat.apart a c) (Rat.apart c b)`.
///
/// **The one place `ℚ`'s decidability is used**, through `Rat.lt_trichotomy`.
/// `CReal` has no analogue — cotransitivity there is a theorem about an
/// undecidable order, not a case split.
fn declare_apart_cotrans(
    k: &mut Kernel,
    p: &RatPrelude,
    apart: NameId,
    ne_of_lt: NameId,
) -> Result<NameId, KernelError> {
    let lg = p.int.nat.logic;
    let q = qctx(k, p);
    let l0 = k.level_zero();

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let hab_ty = q.ne(k, a, b);
    let hab = k.fvar(H1_FV);

    let ap = k.const_(apart, vec![]);
    let goal_l = app2(k, ap, a, c);
    let goal_r = app2(k, ap, c, b);
    let or_c = k.const_(lg.or, vec![]);
    let goal = app2(k, or_c, goal_l, goal_r);

    let lt_ac = q.lt_of(k, a, c);
    let eq_ac = q.eq(k, a, c);
    let lt_ca = q.lt_of(k, c, a);
    let inner_or = app2(k, or_c, eq_ac, lt_ca);

    let tri = {
        let t = k.const_(p.lt_trichotomy, vec![]);
        app2(k, t, a, c)
    };

    let ne_c = k.const_(ne_of_lt, vec![]);
    let inl = k.const_(lg.or_inl, vec![]);
    let inr = k.const_(lg.or_inr, vec![]);

    // Branch 1: `a < c`, so `a` and `c` are apart.
    let branch_lt_ac = {
        let h = k.fvar(H2_FV);
        let ne = t_app(k, ne_c, &[a, c, h]); // Eq a c -> False
        let pf = t_app(k, inl, &[goal_l, goal_r, ne]);
        lam_over(k, H2_FV, lt_ac, pf)
    };
    // Branch 2a: `a = c`, so `c` and `b` are apart because `a` and `b` are.
    let branch_eq = {
        let e = k.fvar(H2_FV);
        let f = k.fvar(H3_FV);
        let eq_cb = q.eq(k, c, b);
        // `Eq.rec` at motive `fun x _ => Eq Rat a x`, refl case `e : Eq a c`,
        // transported along `f : Eq c b` gives `Eq a b`.
        let motive = {
            let x = k.fvar(X_FV);
            let body = q.eq(k, a, x);
            let eq_cx = q.eq(k, c, x);
            let inner = lam_over(k, SCRATCH_FV, eq_cx, body);
            lam_over(k, X_FV, q.rat, inner)
        };
        let rec = k.const_(lg.eq_rec, vec![l0, q.lvl1]);
        let eq_ab = t_app(k, rec, &[q.rat, c, motive, e, b, f]);
        let bad = k.app(hab, eq_ab);
        let ne = lam_over(k, H3_FV, eq_cb, bad);
        let pf = t_app(k, inr, &[goal_l, goal_r, ne]);
        lam_over(k, H2_FV, eq_ac, pf)
    };
    // Branch 2b: `c < a`, so `a` and `c` are apart the other way round.
    let branch_lt_ca = {
        let h = k.fvar(H2_FV);
        let e = k.fvar(H3_FV);
        let symm = k.const_(lg.eq_symm, vec![q.lvl1]);
        let flipped = t_app(k, symm, &[q.rat, a, c, e]); // Eq c a
        let bad = t_app(k, ne_c, &[c, a, h, flipped]);
        let ne = lam_over(k, H3_FV, eq_ac, bad);
        let pf = t_app(k, inl, &[goal_l, goal_r, ne]);
        lam_over(k, H2_FV, lt_ca, pf)
    };

    let elim = k.const_(lg.or_elim, vec![]);
    let branch_rest = {
        let h = k.fvar(SCRATCH_FV + 1);
        let inner = t_app(
            k,
            elim,
            &[eq_ac, lt_ca, goal, h, branch_eq, branch_lt_ca],
        );
        lam_over(k, SCRATCH_FV + 1, inner_or, inner)
    };
    let proof = t_app(
        k,
        elim,
        &[lt_ac, inner_or, goal, tri, branch_lt_ac, branch_rest],
    );

    let value = lam_over(k, C_FV, q.rat, proof);
    let value = lam_over(k, H1_FV, hab_ty, value);
    let value = lam_over(k, B_FV, q.rat, value);
    let value = lam_over(k, A_FV, q.rat, value);

    let ty = pi_over(k, C_FV, q.rat, goal);
    let ty = arrow(k, hab_ty, ty);
    let ty = pi_over(k, B_FV, q.rat, ty);
    let ty = pi_over(k, A_FV, q.rat, ty);

    let name = k.name_str(p.int.rat, "apart_cotrans");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `Rat.apart_compat : forall a b, Eq Rat a b -> Rat.apart a b -> False`.
fn declare_apart_compat(
    k: &mut Kernel,
    p: &RatPrelude,
    apart: NameId,
) -> Result<NameId, KernelError> {
    let q = qctx(k, p);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let e_ty = q.eq(k, a, b);
    let e = k.fvar(H1_FV);
    let ap = k.const_(apart, vec![]);
    let h_ty = app2(k, ap, a, b);
    let h = k.fvar(H2_FV);
    let body = k.app(h, e);

    let value = lam_over(k, H2_FV, h_ty, body);
    let value = lam_over(k, H1_FV, e_ty, value);
    let value = lam_over(k, B_FV, q.rat, value);
    let value = lam_over(k, A_FV, q.rat, value);

    let ty = arrow(k, h_ty, q.false_);
    let ty = arrow(k, e_ty, ty);
    let ty = pi_over(k, B_FV, q.rat, ty);
    let ty = pi_over(k, A_FV, q.rat, ty);

    let name = k.name_str(p.int.rat, "apart_compat");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `Rat.mulInvEx : forall a, Rat.apart a Rat.zero ->
/// Exists Rat (fun b => Eq Rat (Rat.mul a b) Rat.one)`.
///
/// One `Exists.intro` at `Rat.inv a`, closed by
/// `Rat.mul_inv_cancel_of_ne_zero` — `ℚ`'s inverse is TOTAL, so the witness is
/// a plain term. This is exactly the case `CReal` cannot copy.
fn declare_mul_inv_ex(
    k: &mut Kernel,
    p: &RatPrelude,
    apart: NameId,
) -> Result<NameId, KernelError> {
    let lg = p.int.nat.logic;
    let q = qctx(k, p);
    let a = k.fvar(A_FV);
    let ap = k.const_(apart, vec![]);
    let h_ty = app2(k, ap, a, q.zero);
    let h = k.fvar(H1_FV);

    let pred = {
        let b = k.fvar(B_FV);
        let prod = app2(k, q.mul, a, b);
        let body = q.eq(k, prod, q.one);
        lam_over(k, B_FV, q.rat, body)
    };
    let witness = k.app(q.inv, a);
    let cancel = {
        let t = k.const_(p.mul_inv_cancel_of_ne_zero, vec![]);
        app2(k, t, a, h)
    };
    let intro = k.const_(lg.exists_intro, vec![q.lvl1]);
    let proof = t_app(k, intro, &[q.rat, pred, witness, cancel]);

    let value = lam_over(k, H1_FV, h_ty, proof);
    let value = lam_over(k, A_FV, q.rat, value);

    let ex = k.const_(lg.exists_, vec![q.lvl1]);
    let concl = app2(k, ex, q.rat, pred);
    let ty = arrow(k, h_ty, concl);
    let ty = pi_over(k, A_FV, q.rat, ty);

    let name = k.name_str(p.int.rat, "mulInvEx");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `Rat.fieldS : AlgS.Field`.
#[allow(clippy::too_many_arguments)]
fn declare_field_s(
    k: &mut Kernel,
    p: &RatPrelude,
    af: &AlgsField,
    names: [NameId; 5],
) -> Result<NameId, KernelError> {
    let ring = {
        let ofalg = k.const_(p.int.nat.structures_s_extra.comm_ring_ofalg, vec![]);
        let rat_cr = k.const_(p.algebra.rat_comm_ring, vec![]);
        k.app(ofalg, rat_cr)
    };
    let of_c = k.const_(af.of_comm_ring, vec![]);
    let apart = k.const_(names[0], vec![]);
    let mut value = k.app(of_c, ring);
    value = k.app(value, apart);
    for n in &names[1..] {
        let t = k.const_(*n, vec![]);
        value = k.app(value, t);
    }
    let one_ne_zero = k.const_(p.one_ne_zero, vec![]);
    value = k.app(value, one_ne_zero);

    let ty = k.const_(af.ind, vec![]);
    let name = k.name_str(p.int.rat, "fieldS");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `Rat.fieldS_isTight : AlgS.Field.IsTight Rat.fieldS`.
///
/// **The tightness `CReal` cannot prove.** `Not (Not (Eq a b)) -> Eq a b` is
/// stability of equality, and over `ℚ` it is `lt_trichotomy` plus
/// `Rat.ne_of_lt` in the two strict branches. Over `ℝ` it would need a
/// single-index introduction rule for `CReal.lt`, which does not exist —
/// which is why `AlgS.Field` carries tightness as a PREDICATE and not as a
/// field.
fn declare_field_s_is_tight(
    k: &mut Kernel,
    p: &RatPrelude,
    af: &AlgsField,
    field_s: NameId,
    ne_of_lt: NameId,
) -> Result<NameId, KernelError> {
    let lg = p.int.nat.logic;
    let q = qctx(k, p);
    let l0 = k.level_zero();

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let ne_ab = q.ne(k, a, b);
    let nn_ty = arrow(k, ne_ab, q.false_);
    let nn = k.fvar(H1_FV);
    let goal = q.eq(k, a, b);

    let lt_ab = q.lt_of(k, a, b);
    let eq_ab = q.eq(k, a, b);
    let lt_ba = q.lt_of(k, b, a);
    let or_c = k.const_(lg.or, vec![]);
    let inner_or = app2(k, or_c, eq_ab, lt_ba);
    let tri = {
        let t = k.const_(p.lt_trichotomy, vec![]);
        app2(k, t, a, b)
    };
    let ne_c = k.const_(ne_of_lt, vec![]);
    let false_rec = k.const_(lg.false_rec, vec![l0]);
    let false_motive = lam_over(k, SCRATCH_FV, q.false_, goal);

    let branch_lt = {
        let h = k.fvar(H2_FV);
        let ne = {
            let e = k.fvar(H3_FV);
            let bad = t_app(k, ne_c, &[a, b, h, e]);
            lam_over(k, H3_FV, eq_ab, bad)
        };
        let bad = k.app(nn, ne);
        let pf = t_app(k, false_rec, &[false_motive, bad]);
        lam_over(k, H2_FV, lt_ab, pf)
    };
    let branch_eq = {
        let e = k.fvar(H2_FV);
        lam_over(k, H2_FV, eq_ab, e)
    };
    let branch_gt = {
        let h = k.fvar(H2_FV);
        let ne = {
            let e = k.fvar(H3_FV);
            let symm = k.const_(lg.eq_symm, vec![q.lvl1]);
            let flipped = t_app(k, symm, &[q.rat, a, b, e]); // Eq b a
            let bad = t_app(k, ne_c, &[b, a, h, flipped]);
            lam_over(k, H3_FV, eq_ab, bad)
        };
        let bad = k.app(nn, ne);
        let pf = t_app(k, false_rec, &[false_motive, bad]);
        lam_over(k, H2_FV, lt_ba, pf)
    };

    let elim = k.const_(lg.or_elim, vec![]);
    let branch_rest = {
        let h = k.fvar(SCRATCH_FV + 1);
        let inner = t_app(k, elim, &[eq_ab, lt_ba, goal, h, branch_eq, branch_gt]);
        lam_over(k, SCRATCH_FV + 1, inner_or, inner)
    };
    let proof = t_app(
        k,
        elim,
        &[lt_ab, inner_or, goal, tri, branch_lt, branch_rest],
    );

    let value = lam_over(k, H1_FV, nn_ty, proof);
    let value = lam_over(k, B_FV, q.rat, value);
    let value = lam_over(k, A_FV, q.rat, value);

    let ty = {
        let t = k.const_(af.is_tight, vec![]);
        let f = k.const_(field_s, vec![]);
        k.app(t, f)
    };

    let name = k.name_str(p.int.rat, "fieldS_isTight");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// Declare `Rat.fieldS` and everything it needs.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means
/// [`Kernel::add_declaration`] **refused** a proof term.
pub(crate) fn declare_rat_field_s(
    k: &mut Kernel,
    p: &RatPrelude,
) -> Result<RatFieldSNames, KernelError> {
    let af = algs_field(k);
    let ne_of_lt = declare_ne_of_lt(k, p)?;
    let apart = declare_apart(k, p)?;
    let apart_symm = declare_apart_symm(k, p, apart)?;
    let apart_cotrans = declare_apart_cotrans(k, p, apart, ne_of_lt)?;
    let apart_compat = declare_apart_compat(k, p, apart)?;
    let mul_inv_ex = declare_mul_inv_ex(k, p, apart)?;
    let field_s = declare_field_s(
        k,
        p,
        &af,
        [apart, apart_symm, apart_cotrans, apart_compat, mul_inv_ex],
    )?;
    let field_s_is_tight = declare_field_s_is_tight(k, p, &af, field_s, ne_of_lt)?;
    Ok(RatFieldSNames {
        ne_of_lt,
        apart,
        apart_symm,
        apart_cotrans,
        apart_compat,
        mul_inv_ex,
        field_s,
        field_s_is_tight,
    })
}

#[cfg(test)]
#[path = "field_setoid_instance_tests.rs"]
mod field_setoid_instance_tests;
