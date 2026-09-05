//! `AlgS.Poly.*` — roadmap W2-9: the polynomial ring over an **abstract**
//! `AlgS.CommRing`, built by the setoid route (ADR-1595, ADR-1609).
//!
//! # The construction, and why it needs the setoid spine
//!
//! A polynomial over `R` is a **coefficient function** `Nat -> R.carrier`.
//! That is the representation `Rat.polyEval` already uses over `ℚ`
//! (`rat_prelude/polynomial.rs`: "this kernel has no `List` and no tuple
//! type"), lifted to an arbitrary carrier.
//!
//! The carrier is therefore a **function space**, and this is the load-bearing
//! point: on the `Eq`-flavored `Alg.*` spine the polynomial ring is not
//! merely awkward, it is **unreachable**. `Alg.CommGroup`'s law fields are
//! literal `Eq (op a b) (op b a)`, so `Alg`'s `comm` field for polynomials
//! would be `Eq (fun n => R.add (p n) (q n)) (fun n => R.add (q n) (p n))` —
//! an equality of two lambdas, provable only from `funext`, which this kernel
//! does not have and ADR-1595 explicitly did not grant. On the `AlgS` spine
//! the same field is
//! `AlgS.Poly.equiv R (AlgS.Poly.add R p q) (AlgS.Poly.add R q p)`, which
//! delta-beta reduces to `forall n, R.equiv (R.add (p n) (q n)) (R.add (q n)
//! (p n))` and is discharged by `fun p q n => R.addComm (p n) (q n)` — **one
//! application**. See ADR-1609 for the field-by-field cost table.
//!
//! # Build position, and what it costs
//!
//! Everything here is declared at the `AlgS` build position inside
//! `build_nat_prelude_uncached`, where only [`LogicPrelude`] exists: `Nat`,
//! `Nat.zero`, `Nat.succ` and `Nat.rec` are available, and **`Nat.add`,
//! `Nat.sub` and `Nat.le` are not** (they are declared much later). That is
//! why convolution here is not the textbook `sum_{i<=n} p i * q (n-i)` — the
//! subtraction does not exist yet. It is instead an **antidiagonal walk**
//! that needs no arithmetic at all:
//!
//! ```text
//! antidiagFrom g zero     j ≡ g zero j
//! antidiagFrom g (succ i) j ≡ R.add (g (succ i) j) (antidiagFrom g i (succ j))
//! ```
//!
//! so `antidiagFrom g n 0 = g n 0 + (g (n-1) 1 + (… + g 0 n))` — the
//! antidiagonal `i + j = n`, walked downward in `i` and upward in `j`, with
//! the two indices moving in step instead of one being computed from the
//! other. `AlgS.Poly.mul R p q n` is that walk at
//! `g i j := R.mul (p i) (q j)`.
//!
//! # What is declared
//!
//! | name | kind | what it is |
//! |---|---|---|
//! | `AlgS.add_add_add_comm` | theorem | `(a+b)+(c+d) ~ (a+c)+(b+d)`, the middle-four exchange |
//! | `AlgS.Poly.equiv` | definition | pointwise equivalence of coefficient functions |
//! | `AlgS.Poly.add` | definition | pointwise addition |
//! | `AlgS.Poly.zero` | definition | the constant-zero coefficient function |
//! | `AlgS.Poly.neg` | definition | pointwise negation |
//! | `AlgS.Poly.one` | definition | `1` at index 0, `0` elsewhere |
//! | `AlgS.Poly.smul` | definition | scalar multiplication by an element of `R` |
//! | `AlgS.Poly.commGroup` | definition | **the additive group of `R[X]`, a full 16-field `AlgS.CommGroup`** |
//! | `AlgS.Poly.antidiagFrom` | definition | the antidiagonal walk above |
//! | `AlgS.Poly.mul` | definition | convolution product |
//! | `AlgS.Poly.antidiagFrom_congr` | theorem | the walk respects pointwise equivalence |
//! | `AlgS.Poly.antidiagFrom_add` | theorem | the walk is additive |
//! | `AlgS.Poly.mulCongr` | theorem | the `mulCongr` field of `R[X]` |
//! | `AlgS.Poly.distribL` | theorem | the `distribL` field of `R[X]` |
//! | `AlgS.Poly.distribR` | theorem | the `distribR` field of `R[X]` |
//!
//! # Where this stops, and why — stated as an obligation, not a mood
//!
//! `AlgS.Poly` is **not** a declared `AlgS.CommRing` instance. Of the
//! record's 23 fields, 20 are supplied by the declarations above. The ones
//! that are not are `mulOneL`/`mulOneR`, `mulComm` and `mulAssoc`, and the
//! obstruction is the same in all of them: each needs a *reindexing* lemma
//! for `antidiagFrom` (a vanishing-tail collapse, a reversal, and a
//! two-dimensional exchange respectively), none of which the setoid
//! discipline makes harder — they are exactly the lemmas
//! `rat_prelude/diagonal.rs` builds concretely over `ℚ`, where the same
//! obstruction is also still open (`Rat.polyEval_mul` does not exist).
//! ADR-1609 sizes each one. This is a `Quot`-independent gap: `Quot.sound`
//! would not supply a single one of them.

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

use super::structures::{RecordNames, app2, arrow, lam_over, mk_instance, pi_over, sel};
use super::structures_setoid::idx;

// ---------------------------------------------------------------------------
// Free-variable block. Disjoint from `structures_setoid`'s 21_xxx block so a
// term that mixes the two cannot capture.
// ---------------------------------------------------------------------------

const R_FV: u64 = 22_000;
const P_FV: u64 = 22_001;
const Q_FV: u64 = 22_002;
const S_FV: u64 = 22_003;
const N_FV: u64 = 22_010;
const J_FV: u64 = 22_011;
const I_FV: u64 = 22_012;
const A_FV: u64 = 22_020;
const B_FV: u64 = 22_021;
const C_FV: u64 = 22_022;
const D_FV: u64 = 22_023;
const G_FV: u64 = 22_030;
const G1_FV: u64 = 22_031;
const G2_FV: u64 = 22_032;
const H_FV: u64 = 22_040;
const IH_FV: u64 = 22_041;
const HP_FV: u64 = 22_042;
const HQ_FV: u64 = 22_043;
const X_FV: u64 = 22_050;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

// ---------------------------------------------------------------------------
// The selector bundle every declaration in this file opens with: an
// `AlgS.CommRing` free variable and each field of it that anything here uses,
// plus the derived types `Nat`, `Nat -> R.carrier` and `Nat -> Nat -> R.carrier`.
// ---------------------------------------------------------------------------

struct RCtx {
    r: ExprId,
    ring_ty: ExprId,
    carrier: ExprId,
    equiv: ExprId,
    equiv_refl: ExprId,
    equiv_symm: ExprId,
    equiv_trans: ExprId,
    zero: ExprId,
    one: ExprId,
    add: ExprId,
    mul: ExprId,
    add_congr: ExprId,
    mul_congr: ExprId,
    add_assoc: ExprId,
    add_comm: ExprId,
    add_zero: ExprId,
    neg: ExprId,
    neg_congr: ExprId,
    neg_add: ExprId,
    distrib_l: ExprId,
    distrib_r: ExprId,
    /// ADR-1618: the multiplicative fields the four missing `AlgS.CommRing`
    /// fields of `R[X]` are built from.
    mul_assoc: ExprId,
    mul_one_r: ExprId,
    mul_comm: ExprId,
    nat: ExprId,
    /// `Nat -> R.carrier` — a polynomial, as a coefficient function.
    poly: ExprId,
    /// `Nat -> Nat -> R.carrier` — a two-index cell family for the walk.
    cell: ExprId,
}

fn rctx(k: &mut Kernel, lg: &LogicPrelude, cr: &RecordNames) -> RCtx {
    use idx::comm_ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_CONGR, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, EQUIV,
        EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, MUL, MUL_ASSOC, MUL_COMM, MUL_CONGR, MUL_ONE_R, NEG,
        NEG_ADD, NEG_CONGR, ONE, ZERO,
    };
    let ring_ty = k.const_(cr.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, cr, CARRIER, r);
    let nat = k.const_(lg.nat, vec![]);
    let poly = arrow(k, nat, carrier);
    let cell = {
        let inner = arrow(k, nat, carrier);
        arrow(k, nat, inner)
    };
    RCtx {
        r,
        ring_ty,
        carrier,
        equiv: sel(k, cr, EQUIV, r),
        equiv_refl: sel(k, cr, EQUIV_REFL, r),
        equiv_symm: sel(k, cr, EQUIV_SYMM, r),
        equiv_trans: sel(k, cr, EQUIV_TRANS, r),
        zero: sel(k, cr, ZERO, r),
        one: sel(k, cr, ONE, r),
        add: sel(k, cr, ADD, r),
        mul: sel(k, cr, MUL, r),
        add_congr: sel(k, cr, ADD_CONGR, r),
        mul_congr: sel(k, cr, MUL_CONGR, r),
        add_assoc: sel(k, cr, ADD_ASSOC, r),
        add_comm: sel(k, cr, ADD_COMM, r),
        add_zero: sel(k, cr, ADD_ZERO, r),
        neg: sel(k, cr, NEG, r),
        neg_congr: sel(k, cr, NEG_CONGR, r),
        neg_add: sel(k, cr, NEG_ADD, r),
        distrib_l: sel(k, cr, DISTRIB_L, r),
        distrib_r: sel(k, cr, DISTRIB_R, r),
        mul_assoc: sel(k, cr, MUL_ASSOC, r),
        mul_one_r: sel(k, cr, MUL_ONE_R, r),
        mul_comm: sel(k, cr, MUL_COMM, r),
        nat,
        poly,
        cell,
    }
}

impl RCtx {
    fn eq(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.equiv, a, b)
    }
    fn refl(&self, k: &mut Kernel, a: ExprId) -> ExprId {
        k.app(self.equiv_refl, a)
    }
    fn symm(&self, k: &mut Kernel, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        t_app(k, self.equiv_symm, &[a, b, h])
    }
    fn trans(
        &self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        t_app(k, self.equiv_trans, &[a, b, c, h1, h2])
    }
    fn plus(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.add, a, b)
    }
    fn times(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.mul, a, b)
    }
}

// ---------------------------------------------------------------------------
// `AlgS.add_add_add_comm` — the middle-four exchange, over `AlgS.CommRing`.
// ---------------------------------------------------------------------------

/// `AlgS.add_add_add_comm : forall (R : AlgS.CommRing) (a b c d : R.carrier),
/// R.equiv (R.add (R.add a b) (R.add c d)) (R.add (R.add a c) (R.add b d))`.
///
/// Five `equivTrans` steps:
/// `(a+b)+(c+d) ~ a+(b+(c+d)) ~ a+((b+c)+d) ~ a+((c+b)+d) ~ a+(c+(b+d)) ~
/// (a+c)+(b+d)`, using `addAssoc` three times (once symm'd), `addComm` once,
/// and `addCongr` to push the middle rewrite under the outer `a +`.
fn declare_add_add_add_comm(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let cc = k.fvar(C_FV);
    let d = k.fvar(D_FV);

    let ab = c.plus(k, a, b);
    let cd = c.plus(k, cc, d);
    let bc = c.plus(k, b, cc);
    let cb = c.plus(k, cc, b);
    let ac = c.plus(k, a, cc);
    let bd = c.plus(k, b, d);

    let lhs = c.plus(k, ab, cd);
    let rhs = c.plus(k, ac, bd);

    // e0 : (a+b)+(c+d) ~ a+(b+(c+d))
    let b_cd = c.plus(k, b, cd);
    let a_b_cd = c.plus(k, a, b_cd);
    let e0 = t_app(k, c.add_assoc, &[a, b, cd]);

    // e1 : b+(c+d) ~ (b+c)+d      [symm of addAssoc b c d]
    let bc_d = c.plus(k, bc, d);
    let assoc_bcd = t_app(k, c.add_assoc, &[b, cc, d]);
    let e1 = c.symm(k, bc_d, b_cd, assoc_bcd);

    // e2 : (b+c)+d ~ (c+b)+d
    let cb_d = c.plus(k, cb, d);
    let comm_bc = t_app(k, c.add_comm, &[b, cc]);
    let refl_d = c.refl(k, d);
    let e2 = t_app(k, c.add_congr, &[bc, cb, d, d, comm_bc, refl_d]);

    // e3 : (c+b)+d ~ c+(b+d)
    let c_bd = c.plus(k, cc, bd);
    let e3 = t_app(k, c.add_assoc, &[cc, b, d]);

    // inner : b+(c+d) ~ c+(b+d)
    let inner = c.trans(k, b_cd, bc_d, cb_d, e1, e2);
    let inner = c.trans(k, b_cd, cb_d, c_bd, inner, e3);

    // e4 : a+(b+(c+d)) ~ a+(c+(b+d))
    let refl_a = c.refl(k, a);
    let e4 = t_app(k, c.add_congr, &[a, a, b_cd, c_bd, refl_a, inner]);

    let a_c_bd = c.plus(k, a, c_bd);
    let step1 = c.trans(k, lhs, a_b_cd, a_c_bd, e0, e4);

    // e5 : a+(c+(b+d)) ~ (a+c)+(b+d)
    let assoc_acbd = t_app(k, c.add_assoc, &[a, cc, bd]);
    let e5 = c.symm(k, rhs, a_c_bd, assoc_acbd);

    let proof = c.trans(k, lhs, a_c_bd, rhs, step1, e5);

    let value = lam_over(k, D_FV, c.carrier, proof);
    let value = lam_over(k, C_FV, c.carrier, value);
    let value = lam_over(k, B_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = c.eq(k, lhs, rhs);
    let ty = pi_over(k, D_FV, c.carrier, concl);
    let ty = pi_over(k, C_FV, c.carrier, ty);
    let ty = pi_over(k, B_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(algs_p, "add_add_add_comm");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// The coefficient-function operations.
// ---------------------------------------------------------------------------

/// `AlgS.Poly.equiv : forall (R : AlgS.CommRing),
/// (Nat -> R.carrier) -> (Nat -> R.carrier) -> Prop
/// := fun R p q => forall n, R.equiv (p n) (q n)`.
///
/// This IS the equality of the polynomial ring, and it is the whole reason
/// the construction is reachable: it says nothing about the two functions as
/// kernel objects, only that they agree coefficientwise up to `R`'s own
/// equivalence.
fn declare_poly_equiv(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let p = k.fvar(P_FV);
    let q = k.fvar(Q_FV);
    let n = k.fvar(N_FV);
    let pn = k.app(p, n);
    let qn = k.app(q, n);
    let body = c.eq(k, pn, qn);
    let body = pi_over(k, N_FV, c.nat, body);
    let value = lam_over(k, Q_FV, c.poly, body);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = arrow(k, c.poly, prop);
    let ty = arrow(k, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "equiv");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Poly.add R p q := fun n => R.add (p n) (q n)`.
fn declare_poly_add(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let p = k.fvar(P_FV);
    let q = k.fvar(Q_FV);
    let n = k.fvar(N_FV);
    let pn = k.app(p, n);
    let qn = k.app(q, n);
    let body = c.plus(k, pn, qn);
    let body = lam_over(k, N_FV, c.nat, body);
    let value = lam_over(k, Q_FV, c.poly, body);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let ty = arrow(k, c.poly, c.poly);
    let ty = arrow(k, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "add");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Poly.zero R := fun _ => R.zero`.
fn declare_poly_zero(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let body = lam_over(k, N_FV, c.nat, c.zero);
    let value = lam_over(k, R_FV, c.ring_ty, body);
    let ty = pi_over(k, R_FV, c.ring_ty, c.poly);

    let name = k.name_str(poly_ns, "zero");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Poly.neg R p := fun n => R.neg (p n)`.
fn declare_poly_neg(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let p = k.fvar(P_FV);
    let n = k.fvar(N_FV);
    let pn = k.app(p, n);
    let body = k.app(c.neg, pn);
    let body = lam_over(k, N_FV, c.nat, body);
    let value = lam_over(k, P_FV, c.poly, body);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let ty = arrow(k, c.poly, c.poly);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "neg");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Poly.one R := fun n => Nat.rec (motive := fun _ => R.carrier)
/// R.one (fun _ _ => R.zero) n` — the constant polynomial `1`: `R.one` at
/// index `0`, `R.zero` at every successor index.
fn declare_poly_one(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let motive = lam_over(k, X_FV, c.nat, c.carrier);
    let minor_succ = {
        let inner = lam_over(k, IH_FV, c.carrier, c.zero);
        lam_over(k, I_FV, c.nat, inner)
    };
    let n = k.fvar(N_FV);
    let rec = k.const_(lg.nat_rec, vec![l1]);
    let body = t_app(k, rec, &[motive, c.one, minor_succ, n]);
    let body = lam_over(k, N_FV, c.nat, body);
    let value = lam_over(k, R_FV, c.ring_ty, body);
    let ty = pi_over(k, R_FV, c.ring_ty, c.poly);

    let name = k.name_str(poly_ns, "one");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Poly.smul R a p := fun n => R.mul a (p n)` — the scalar action of
/// `R` on `R[X]`.
fn declare_poly_smul(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let a = k.fvar(A_FV);
    let p = k.fvar(P_FV);
    let n = k.fvar(N_FV);
    let pn = k.app(p, n);
    let body = c.times(k, a, pn);
    let body = lam_over(k, N_FV, c.nat, body);
    let value = lam_over(k, P_FV, c.poly, body);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let ty = arrow(k, c.poly, c.poly);
    let ty = arrow(k, c.carrier, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "smul");
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
// `AlgS.Poly.commGroup` — the additive group of `R[X]`, a full 16-field
// `AlgS.CommGroup` instance.
// ---------------------------------------------------------------------------

/// `AlgS.Poly.commGroup : AlgS.CommRing -> AlgS.CommGroup`.
///
/// Every field is `R`'s corresponding field applied at the coefficient index,
/// which is exactly what the setoid presentation buys: the record's law
/// fields are `AlgS.Poly.equiv R lhs rhs`, which delta-beta reduces to
/// `forall n, R.equiv (lhs n) (rhs n)`, so `fun p q n => R.addComm (p n)
/// (q n)` type-checks directly. On the `Eq` spine the same field would be an
/// equality of two lambdas and would need `funext`.
///
/// Only `identL` and `invL` need more than one application, and for the same
/// reason `AlgS.CommRing.toCommGroupS` does: `AlgS.CommRing` carries
/// `addZero`/`negAdd` on the RIGHT only, so the left-sided fields are derived
/// through `addComm` with one `equivTrans` each.
#[allow(clippy::too_many_lines)]
fn declare_poly_comm_group(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    comm_group: &RecordNames,
    names: &PolyOpNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);

    let equiv_c = {
        let t = k.const_(names.equiv, vec![]);
        k.app(t, c.r)
    };
    let add_c = {
        let t = k.const_(names.add, vec![]);
        k.app(t, c.r)
    };
    let zero_c = {
        let t = k.const_(names.zero, vec![]);
        k.app(t, c.r)
    };
    let neg_c = {
        let t = k.const_(names.neg, vec![]);
        k.app(t, c.r)
    };

    // 2. equivRefl : forall p, equiv p p
    let f_refl = {
        let p = k.fvar(P_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = c.refl(k, pn);
        let body = lam_over(k, N_FV, c.nat, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 3. equivSymm
    let f_symm = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let hyp = app2(k, equiv_c, p, q);
        let h = k.fvar(H_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let hn = k.app(h, n);
        let body = c.symm(k, pn, qn, hn);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, H_FV, hyp, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 4. equivTrans
    let f_trans = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let s = k.fvar(S_FV);
        let hyp1 = app2(k, equiv_c, p, q);
        let hyp2 = app2(k, equiv_c, q, s);
        let h1 = k.fvar(HP_FV);
        let h2 = k.fvar(HQ_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let sn = k.app(s, n);
        let h1n = k.app(h1, n);
        let h2n = k.app(h2, n);
        let body = c.trans(k, pn, qn, sn, h1n, h2n);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, HQ_FV, hyp2, body);
        let body = lam_over(k, HP_FV, hyp1, body);
        let body = lam_over(k, S_FV, c.poly, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 6. opCongr
    let f_add_congr = {
        let p = k.fvar(P_FV);
        let pp = k.fvar(A_FV);
        let q = k.fvar(Q_FV);
        let qq = k.fvar(B_FV);
        let hyp1 = app2(k, equiv_c, p, pp);
        let hyp2 = app2(k, equiv_c, q, qq);
        let h1 = k.fvar(HP_FV);
        let h2 = k.fvar(HQ_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let ppn = k.app(pp, n);
        let qn = k.app(q, n);
        let qqn = k.app(qq, n);
        let h1n = k.app(h1, n);
        let h2n = k.app(h2, n);
        let body = t_app(k, c.add_congr, &[pn, ppn, qn, qqn, h1n, h2n]);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, HQ_FV, hyp2, body);
        let body = lam_over(k, HP_FV, hyp1, body);
        let body = lam_over(k, B_FV, c.poly, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        let body = lam_over(k, A_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 9. invCongr
    let f_neg_congr = {
        let p = k.fvar(P_FV);
        let pp = k.fvar(A_FV);
        let hyp = app2(k, equiv_c, p, pp);
        let h = k.fvar(H_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let ppn = k.app(pp, n);
        let hn = k.app(h, n);
        let body = t_app(k, c.neg_congr, &[pn, ppn, hn]);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, H_FV, hyp, body);
        let body = lam_over(k, A_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 10. assoc
    let f_assoc = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let s = k.fvar(S_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let sn = k.app(s, n);
        let body = t_app(k, c.add_assoc, &[pn, qn, sn]);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, S_FV, c.poly, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 11. identL : forall p, equiv (add zero p) p — derived through addComm.
    let f_ident_l = {
        let p = k.fvar(P_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let z_pn = c.plus(k, c.zero, pn);
        let pn_z = c.plus(k, pn, c.zero);
        let comm = t_app(k, c.add_comm, &[c.zero, pn]);
        let az = k.app(c.add_zero, pn);
        let body = c.trans(k, z_pn, pn_z, pn, comm, az);
        let body = lam_over(k, N_FV, c.nat, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 12. identR
    let f_ident_r = {
        let p = k.fvar(P_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = k.app(c.add_zero, pn);
        let body = lam_over(k, N_FV, c.nat, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 13. invL : forall p, equiv (add (neg p) p) zero — through addComm.
    let f_inv_l = {
        let p = k.fvar(P_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let npn = k.app(c.neg, pn);
        let np_p = c.plus(k, npn, pn);
        let p_np = c.plus(k, pn, npn);
        let comm = t_app(k, c.add_comm, &[npn, pn]);
        let na = k.app(c.neg_add, pn);
        let body = c.trans(k, np_p, p_np, c.zero, comm, na);
        let body = lam_over(k, N_FV, c.nat, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 14. invR
    let f_inv_r = {
        let p = k.fvar(P_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = k.app(c.neg_add, pn);
        let body = lam_over(k, N_FV, c.nat, body);
        lam_over(k, P_FV, c.poly, body)
    };
    // 15. comm
    let f_comm = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let body = t_app(k, c.add_comm, &[pn, qn]);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };

    let value = mk_instance(
        k,
        comm_group,
        &[
            c.poly,
            equiv_c,
            f_refl,
            f_symm,
            f_trans,
            add_c,
            f_add_congr,
            zero_c,
            neg_c,
            f_neg_congr,
            f_assoc,
            f_ident_l,
            f_ident_r,
            f_inv_l,
            f_inv_r,
            f_comm,
        ],
    );
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let cg_ty = k.const_(comm_group.ind, vec![]);
    let ty = arrow(k, c.ring_ty, cg_ty);

    let name = k.name_str(poly_ns, "commGroup");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// Convolution: the antidiagonal walk, and the product built on it.
// ---------------------------------------------------------------------------

/// `AlgS.Poly.antidiagFrom : forall (R : AlgS.CommRing),
/// (Nat -> Nat -> R.carrier) -> Nat -> Nat -> R.carrier`, by `Nat.rec` on the
/// FIRST index with motive `fun _ => Nat -> R.carrier` (so the second index
/// travels through the recursion).
fn declare_antidiag_from(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let g = k.fvar(G_FV);
    let motive = {
        let cod = arrow(k, c.nat, c.carrier);
        lam_over(k, X_FV, c.nat, cod)
    };
    let minor_zero = {
        let j = k.fvar(J_FV);
        let zero_n = k.const_(lg.nat_zero, vec![]);
        let body = t_app(k, g, &[zero_n, j]);
        lam_over(k, J_FV, c.nat, body)
    };
    let minor_succ = {
        let i = k.fvar(I_FV);
        let ih = k.fvar(IH_FV);
        let j = k.fvar(J_FV);
        let succ_c = k.const_(lg.nat_succ, vec![]);
        let si = k.app(succ_c, i);
        let sj = k.app(succ_c, j);
        let head = t_app(k, g, &[si, j]);
        let tail = k.app(ih, sj);
        let body = c.plus(k, head, tail);
        let body = lam_over(k, J_FV, c.nat, body);
        let ih_ty = arrow(k, c.nat, c.carrier);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, c.nat, body)
    };
    let i = k.fvar(I_FV);
    let rec = k.const_(lg.nat_rec, vec![l1]);
    let body = t_app(k, rec, &[motive, minor_zero, minor_succ, i]);
    let value = lam_over(k, I_FV, c.nat, body);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let ty = {
        let inner = arrow(k, c.nat, c.carrier);
        let inner = arrow(k, c.nat, inner);
        let inner = arrow(k, c.cell, inner);
        pi_over(k, R_FV, c.ring_ty, inner)
    };

    let name = k.name_str(poly_ns, "antidiagFrom");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `fun i j => R.mul (p i) (q j)` — the cell family convolution walks.
fn mul_cells(k: &mut Kernel, c: &RCtx, p: ExprId, q: ExprId) -> ExprId {
    let i = k.fvar(I_FV);
    let j = k.fvar(J_FV);
    let pi = k.app(p, i);
    let qj = k.app(q, j);
    let body = c.times(k, pi, qj);
    let body = lam_over(k, J_FV, c.nat, body);
    lam_over(k, I_FV, c.nat, body)
}

/// `AlgS.Poly.mul R p q := fun n => antidiagFrom R (fun i j => R.mul (p i)
/// (q j)) n Nat.zero` — the convolution
/// `p n · q 0 + (p (n-1) · q 1 + (… + p 0 · q n))`, with the two indices
/// walked in step rather than one subtracted from the other.
fn declare_poly_mul(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let p = k.fvar(P_FV);
    let q = k.fvar(Q_FV);
    let cells = mul_cells(k, &c, p, q);
    let n = k.fvar(N_FV);
    let zero_n = k.const_(lg.nat_zero, vec![]);
    let a = k.const_(antidiag, vec![]);
    let body = t_app(k, a, &[c.r, cells, n, zero_n]);
    let body = lam_over(k, N_FV, c.nat, body);
    let value = lam_over(k, Q_FV, c.poly, body);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let ty = arrow(k, c.poly, c.poly);
    let ty = arrow(k, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "mul");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// The two walk lemmas, and the three ring-field theorems they discharge.
// ---------------------------------------------------------------------------

/// `AlgS.Poly.antidiagFrom_congr : forall R g g',
/// (forall i j, R.equiv (g i j) (g' i j)) ->
/// forall i j, R.equiv (antidiagFrom R g i j) (antidiagFrom R g' i j)`.
///
/// `Nat.rec` on the first index with motive `fun i => forall j, …`, so the
/// induction hypothesis is available at EVERY second index — which is what
/// the walk's `succ` step needs (it calls itself at `succ j`, not `j`).
fn declare_antidiag_congr(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let g = k.fvar(G_FV);
    let g1 = k.fvar(G1_FV);

    let hyp_ty = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let lhs = t_app(k, g, &[i, j]);
        let rhs = t_app(k, g1, &[i, j]);
        let body = c.eq(k, lhs, rhs);
        let body = pi_over(k, J_FV, c.nat, body);
        pi_over(k, I_FV, c.nat, body)
    };
    let h = k.fvar(H_FV);

    let motive_body = |k: &mut Kernel, c: &RCtx, i: ExprId| {
        let j = k.fvar(J_FV);
        let a1 = k.const_(antidiag, vec![]);
        let lhs = t_app(k, a1, &[c.r, g, i, j]);
        let a2 = k.const_(antidiag, vec![]);
        let rhs = t_app(k, a2, &[c.r, g1, i, j]);
        let body = c.eq(k, lhs, rhs);
        pi_over(k, J_FV, c.nat, body)
    };
    let motive = {
        let i = k.fvar(I_FV);
        let body = motive_body(k, &c, i);
        lam_over(k, I_FV, c.nat, body)
    };
    let minor_zero = {
        let j = k.fvar(J_FV);
        let zero_n = k.const_(lg.nat_zero, vec![]);
        let body = t_app(k, h, &[zero_n, j]);
        lam_over(k, J_FV, c.nat, body)
    };
    let minor_succ = {
        let i = k.fvar(I_FV);
        let ih_ty = motive_body(k, &c, i);
        let ih = k.fvar(IH_FV);
        let j = k.fvar(J_FV);
        let succ_c = k.const_(lg.nat_succ, vec![]);
        let si = k.app(succ_c, i);
        let sj = k.app(succ_c, j);
        let head_l = t_app(k, g, &[si, j]);
        let head_r = t_app(k, g1, &[si, j]);
        let a1 = k.const_(antidiag, vec![]);
        let tail_l = t_app(k, a1, &[c.r, g, i, sj]);
        let a2 = k.const_(antidiag, vec![]);
        let tail_r = t_app(k, a2, &[c.r, g1, i, sj]);
        let h_head = t_app(k, h, &[si, j]);
        let h_tail = k.app(ih, sj);
        let body = t_app(
            k,
            c.add_congr,
            &[head_l, head_r, tail_l, tail_r, h_head, h_tail],
        );
        let body = lam_over(k, J_FV, c.nat, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, c.nat, body)
    };
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let proof = t_app(k, rec, &[motive, minor_zero, minor_succ]);

    let value = lam_over(k, H_FV, hyp_ty, proof);
    let value = lam_over(k, G1_FV, c.cell, value);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let i = k.fvar(I_FV);
        let body = motive_body(k, &c, i);
        pi_over(k, I_FV, c.nat, body)
    };
    let ty = pi_over(k, H_FV, hyp_ty, concl);
    let ty = pi_over(k, G1_FV, c.cell, ty);
    let ty = pi_over(k, G_FV, c.cell, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "antidiagFrom_congr");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.antidiagFrom_add : forall R g g1 g2,
/// (forall i j, R.equiv (g i j) (R.add (g1 i j) (g2 i j))) ->
/// forall i j, R.equiv (antidiagFrom R g i j)
///                     (R.add (antidiagFrom R g1 i j) (antidiagFrom R g2 i j))`.
///
/// The successor step is one `addCongr` (hypothesis at the head, induction
/// hypothesis at `succ j` for the tail) followed by one
/// `AlgS.add_add_add_comm` to exchange the middle two summands. That exchange
/// is the only real content; everything else is the walk unfolding.
fn declare_antidiag_add(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    add4: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let g = k.fvar(G_FV);
    let g1 = k.fvar(G1_FV);
    let g2 = k.fvar(G2_FV);

    let hyp_ty = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let lhs = t_app(k, g, &[i, j]);
        let r1 = t_app(k, g1, &[i, j]);
        let r2 = t_app(k, g2, &[i, j]);
        let rhs = c.plus(k, r1, r2);
        let body = c.eq(k, lhs, rhs);
        let body = pi_over(k, J_FV, c.nat, body);
        pi_over(k, I_FV, c.nat, body)
    };
    let h = k.fvar(H_FV);

    let motive_body = |k: &mut Kernel, c: &RCtx, i: ExprId| {
        let j = k.fvar(J_FV);
        let a0 = k.const_(antidiag, vec![]);
        let lhs = t_app(k, a0, &[c.r, g, i, j]);
        let a1 = k.const_(antidiag, vec![]);
        let w1 = t_app(k, a1, &[c.r, g1, i, j]);
        let a2 = k.const_(antidiag, vec![]);
        let w2 = t_app(k, a2, &[c.r, g2, i, j]);
        let rhs = c.plus(k, w1, w2);
        let body = c.eq(k, lhs, rhs);
        pi_over(k, J_FV, c.nat, body)
    };
    let motive = {
        let i = k.fvar(I_FV);
        let body = motive_body(k, &c, i);
        lam_over(k, I_FV, c.nat, body)
    };
    let minor_zero = {
        let j = k.fvar(J_FV);
        let zero_n = k.const_(lg.nat_zero, vec![]);
        let body = t_app(k, h, &[zero_n, j]);
        lam_over(k, J_FV, c.nat, body)
    };
    let minor_succ = {
        let i = k.fvar(I_FV);
        let ih_ty = motive_body(k, &c, i);
        let ih = k.fvar(IH_FV);
        let j = k.fvar(J_FV);
        let succ_c = k.const_(lg.nat_succ, vec![]);
        let si = k.app(succ_c, i);
        let sj = k.app(succ_c, j);

        let head = t_app(k, g, &[si, j]);
        let head1 = t_app(k, g1, &[si, j]);
        let head2 = t_app(k, g2, &[si, j]);
        let head_sum = c.plus(k, head1, head2);
        let a0 = k.const_(antidiag, vec![]);
        let tail = t_app(k, a0, &[c.r, g, i, sj]);
        let a1 = k.const_(antidiag, vec![]);
        let tail1 = t_app(k, a1, &[c.r, g1, i, sj]);
        let a2 = k.const_(antidiag, vec![]);
        let tail2 = t_app(k, a2, &[c.r, g2, i, sj]);
        let tail_sum = c.plus(k, tail1, tail2);

        let lhs = c.plus(k, head, tail);
        let mid = c.plus(k, head_sum, tail_sum);
        let out1 = c.plus(k, head1, tail1);
        let out2 = c.plus(k, head2, tail2);
        let rhs = c.plus(k, out1, out2);

        let h_head = t_app(k, h, &[si, j]);
        let h_tail = k.app(ih, sj);
        let step1 = t_app(
            k,
            c.add_congr,
            &[head, head_sum, tail, tail_sum, h_head, h_tail],
        );
        let step2 = {
            let t = k.const_(add4, vec![]);
            t_app(k, t, &[c.r, head1, head2, tail1, tail2])
        };
        let body = c.trans(k, lhs, mid, rhs, step1, step2);
        let body = lam_over(k, J_FV, c.nat, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, c.nat, body)
    };
    let rec = k.const_(lg.nat_rec, vec![l0]);
    let proof = t_app(k, rec, &[motive, minor_zero, minor_succ]);

    let value = lam_over(k, H_FV, hyp_ty, proof);
    let value = lam_over(k, G2_FV, c.cell, value);
    let value = lam_over(k, G1_FV, c.cell, value);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let i = k.fvar(I_FV);
        let body = motive_body(k, &c, i);
        pi_over(k, I_FV, c.nat, body)
    };
    let ty = pi_over(k, H_FV, hyp_ty, concl);
    let ty = pi_over(k, G2_FV, c.cell, ty);
    let ty = pi_over(k, G1_FV, c.cell, ty);
    let ty = pi_over(k, G_FV, c.cell, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "antidiagFrom_add");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.mulCongr : forall R p p' q q', Poly.equiv R p p' ->
/// Poly.equiv R q q' -> Poly.equiv R (mul R p q) (mul R p' q')` — the
/// `mulCongr` field `R[X]` would need as an `AlgS.CommRing`, discharged by
/// `antidiagFrom_congr` at the cell family `fun i j => p i * q j`.
fn declare_poly_mul_congr(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    congr: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let equiv_c = {
        let t = k.const_(names.equiv, vec![]);
        k.app(t, c.r)
    };
    let mul_c = {
        let t = k.const_(names.mul, vec![]);
        k.app(t, c.r)
    };

    let p = k.fvar(P_FV);
    let pp = k.fvar(A_FV);
    let q = k.fvar(Q_FV);
    let qq = k.fvar(B_FV);
    let hyp1 = app2(k, equiv_c, p, pp);
    let hyp2 = app2(k, equiv_c, q, qq);
    let h1 = k.fvar(HP_FV);
    let h2 = k.fvar(HQ_FV);

    let cells = mul_cells(k, &c, p, q);
    let cells2 = mul_cells(k, &c, pp, qq);
    let cell_hyp = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let pi = k.app(p, i);
        let ppi = k.app(pp, i);
        let qj = k.app(q, j);
        let qqj = k.app(qq, j);
        let h1i = k.app(h1, i);
        let h2j = k.app(h2, j);
        let body = t_app(k, c.mul_congr, &[pi, ppi, qj, qqj, h1i, h2j]);
        let body = lam_over(k, J_FV, c.nat, body);
        lam_over(k, I_FV, c.nat, body)
    };
    let n = k.fvar(N_FV);
    let zero_n = k.const_(lg.nat_zero, vec![]);
    let applied = {
        let t = k.const_(congr, vec![]);
        t_app(k, t, &[c.r, cells, cells2, cell_hyp, n, zero_n])
    };
    let body = lam_over(k, N_FV, c.nat, applied);
    let value = lam_over(k, HQ_FV, hyp2, body);
    let value = lam_over(k, HP_FV, hyp1, value);
    let value = lam_over(k, B_FV, c.poly, value);
    let value = lam_over(k, Q_FV, c.poly, value);
    let value = lam_over(k, A_FV, c.poly, value);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let lhs = app2(k, mul_c, p, q);
        let rhs = app2(k, mul_c, pp, qq);
        app2(k, equiv_c, lhs, rhs)
    };
    let ty = pi_over(k, HQ_FV, hyp2, concl);
    let ty = pi_over(k, HP_FV, hyp1, ty);
    let ty = pi_over(k, B_FV, c.poly, ty);
    let ty = pi_over(k, Q_FV, c.poly, ty);
    let ty = pi_over(k, A_FV, c.poly, ty);
    let ty = pi_over(k, P_FV, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "mulCongr");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.distribL : forall R p q s, Poly.equiv R (mul R p (add R q s))
/// (add R (mul R p q) (mul R p s))`.
fn declare_poly_distrib_l(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    add_lemma: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let equiv_c = {
        let t = k.const_(names.equiv, vec![]);
        k.app(t, c.r)
    };
    let add_c = {
        let t = k.const_(names.add, vec![]);
        k.app(t, c.r)
    };
    let mul_c = {
        let t = k.const_(names.mul, vec![]);
        k.app(t, c.r)
    };

    let p = k.fvar(P_FV);
    let q = k.fvar(Q_FV);
    let s = k.fvar(S_FV);
    let qs = app2(k, add_c, q, s);

    let cells = mul_cells(k, &c, p, qs);
    let cells1 = mul_cells(k, &c, p, q);
    let cells2 = mul_cells(k, &c, p, s);
    let cell_hyp = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let pi = k.app(p, i);
        let qj = k.app(q, j);
        let sj = k.app(s, j);
        let body = t_app(k, c.distrib_l, &[pi, qj, sj]);
        let body = lam_over(k, J_FV, c.nat, body);
        lam_over(k, I_FV, c.nat, body)
    };
    let n = k.fvar(N_FV);
    let zero_n = k.const_(lg.nat_zero, vec![]);
    let applied = {
        let t = k.const_(add_lemma, vec![]);
        t_app(k, t, &[c.r, cells, cells1, cells2, cell_hyp, n, zero_n])
    };
    let body = lam_over(k, N_FV, c.nat, applied);
    let value = lam_over(k, S_FV, c.poly, body);
    let value = lam_over(k, Q_FV, c.poly, value);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let lhs = app2(k, mul_c, p, qs);
        let m1 = app2(k, mul_c, p, q);
        let m2 = app2(k, mul_c, p, s);
        let rhs = app2(k, add_c, m1, m2);
        app2(k, equiv_c, lhs, rhs)
    };
    let ty = pi_over(k, S_FV, c.poly, concl);
    let ty = pi_over(k, Q_FV, c.poly, ty);
    let ty = pi_over(k, P_FV, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "distribL");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.distribR : forall R p q s, Poly.equiv R (mul R (add R p q) s)
/// (add R (mul R p s) (mul R q s))`.
fn declare_poly_distrib_r(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    add_lemma: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let equiv_c = {
        let t = k.const_(names.equiv, vec![]);
        k.app(t, c.r)
    };
    let add_c = {
        let t = k.const_(names.add, vec![]);
        k.app(t, c.r)
    };
    let mul_c = {
        let t = k.const_(names.mul, vec![]);
        k.app(t, c.r)
    };

    let p = k.fvar(P_FV);
    let q = k.fvar(Q_FV);
    let s = k.fvar(S_FV);
    let pq = app2(k, add_c, p, q);

    let cells = mul_cells(k, &c, pq, s);
    let cells1 = mul_cells(k, &c, p, s);
    let cells2 = mul_cells(k, &c, q, s);
    let cell_hyp = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let pi = k.app(p, i);
        let qi = k.app(q, i);
        let sj = k.app(s, j);
        let body = t_app(k, c.distrib_r, &[pi, qi, sj]);
        let body = lam_over(k, J_FV, c.nat, body);
        lam_over(k, I_FV, c.nat, body)
    };
    let n = k.fvar(N_FV);
    let zero_n = k.const_(lg.nat_zero, vec![]);
    let applied = {
        let t = k.const_(add_lemma, vec![]);
        t_app(k, t, &[c.r, cells, cells1, cells2, cell_hyp, n, zero_n])
    };
    let body = lam_over(k, N_FV, c.nat, applied);
    let value = lam_over(k, S_FV, c.poly, body);
    let value = lam_over(k, Q_FV, c.poly, value);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let lhs = app2(k, mul_c, pq, s);
        let m1 = app2(k, mul_c, p, s);
        let m2 = app2(k, mul_c, q, s);
        let rhs = app2(k, add_c, m1, m2);
        app2(k, equiv_c, lhs, rhs)
    };
    let ty = pi_over(k, S_FV, c.poly, concl);
    let ty = pi_over(k, Q_FV, c.poly, ty);
    let ty = pi_over(k, P_FV, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "distribR");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// ADR-1618: the reindexing lemmas for the walk, and the four `AlgS.CommRing`
// fields ADR-1609 left open.
//
// Every one of these is proved by `Nat.rec` on the FIRST walk index with a
// motive that quantifies over the cell family (`fun i => forall g, ...`) or
// over the second index (`fun i => forall j, ...`). That generalization is
// the whole trick: the walk's successor step calls itself at `succ j` and at
// a SHIFTED family, so an induction hypothesis fixed at one `j` or one `g` is
// unusable. With it, none of these lemmas needs `Nat.add`, `Nat.sub` or any
// other arithmetic -- which is why this module stays at the `AlgS` build
// position. ADR-1618 records the measurement.
// ---------------------------------------------------------------------------

/// The outer `Nat.rec` variable, disjoint from `I_FV`/`J_FV` so a nested
/// walk's own indices cannot capture it.
const M_FV: u64 = 22_013;
/// A ring element pulled through a walk (`antidiagFrom_mul_right`).
const EL_FV: u64 = 22_052;

fn succ_of(k: &mut Kernel, lg: &LogicPrelude, e: ExprId) -> ExprId {
    let s = k.const_(lg.nat_succ, vec![]);
    k.app(s, e)
}

fn zero_of(k: &mut Kernel, lg: &LogicPrelude) -> ExprId {
    k.const_(lg.nat_zero, vec![])
}

/// `AlgS.Poly.antidiagFrom R g i j`.
fn walk(k: &mut Kernel, c: &RCtx, antidiag: NameId, g: ExprId, i: ExprId, j: ExprId) -> ExprId {
    let a = k.const_(antidiag, vec![]);
    t_app(k, a, &[c.r, g, i, j])
}

/// `fun a b => g a (succ b)` — the walk's second index shifted up.
fn shift_second(k: &mut Kernel, lg: &LogicPrelude, c: &RCtx, g: ExprId) -> ExprId {
    let i = k.fvar(I_FV);
    let j = k.fvar(J_FV);
    let sj = succ_of(k, lg, j);
    let body = t_app(k, g, &[i, sj]);
    let body = lam_over(k, J_FV, c.nat, body);
    lam_over(k, I_FV, c.nat, body)
}

/// `fun a b => g (succ a) b` — the walk's first index shifted up.
fn shift_first(k: &mut Kernel, lg: &LogicPrelude, c: &RCtx, g: ExprId) -> ExprId {
    let i = k.fvar(I_FV);
    let j = k.fvar(J_FV);
    let si = succ_of(k, lg, i);
    let body = t_app(k, g, &[si, j]);
    let body = lam_over(k, J_FV, c.nat, body);
    lam_over(k, I_FV, c.nat, body)
}

/// `fun a b => g (succ a) (succ b)` — both indices shifted up.
fn shift_both(k: &mut Kernel, lg: &LogicPrelude, c: &RCtx, g: ExprId) -> ExprId {
    let i = k.fvar(I_FV);
    let j = k.fvar(J_FV);
    let si = succ_of(k, lg, i);
    let sj = succ_of(k, lg, j);
    let body = t_app(k, g, &[si, sj]);
    let body = lam_over(k, J_FV, c.nat, body);
    lam_over(k, I_FV, c.nat, body)
}

/// `fun a b => g b a` — the cell family transposed.
fn transpose_cells(k: &mut Kernel, c: &RCtx, g: ExprId) -> ExprId {
    let i = k.fvar(I_FV);
    let j = k.fvar(J_FV);
    let body = t_app(k, g, &[j, i]);
    let body = lam_over(k, J_FV, c.nat, body);
    lam_over(k, I_FV, c.nat, body)
}

/// `AlgS.Poly.antidiagFrom_shift : forall R g i j,
/// R.equiv (antidiagFrom R g i (succ j))
///         (antidiagFrom R (fun a b => g a (succ b)) i j)`.
///
/// **The shift lemma.** Starting the walk one step further along the second
/// index is the same as walking the shifted family from where you were. It is
/// what replaces `j + n` — the index the textbook antidiagonal names and that
/// cannot be written here, `Nat.add` not existing at this build position.
///
/// `Nat.rec` on `i` with motive `fun i => forall j, …`; the base is `refl`
/// (both sides reduce to `g 0 (succ j)`) and the step is one `addCongr` whose
/// second component is the induction hypothesis at `succ j`.
fn declare_antidiag_shift(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let g = k.fvar(G_FV);
    let gs = shift_second(k, lg, &c, g);

    let motive_body = |k: &mut Kernel, c: &RCtx, i: ExprId| {
        let j = k.fvar(J_FV);
        let sj = succ_of(k, lg, j);
        let lhs = walk(k, c, antidiag, g, i, sj);
        let rhs = walk(k, c, antidiag, gs, i, j);
        let body = c.eq(k, lhs, rhs);
        pi_over(k, J_FV, c.nat, body)
    };
    let motive = {
        let i = k.fvar(I_FV);
        let body = motive_body(k, &c, i);
        lam_over(k, I_FV, c.nat, body)
    };
    let minor_zero = {
        let j = k.fvar(J_FV);
        let sj = succ_of(k, lg, j);
        let zero_n = zero_of(k, lg);
        let lhs = walk(k, &c, antidiag, g, zero_n, sj);
        let body = c.refl(k, lhs);
        lam_over(k, J_FV, c.nat, body)
    };
    let minor_succ = {
        let i = k.fvar(I_FV);
        let ih_ty = motive_body(k, &c, i);
        let ih = k.fvar(IH_FV);
        let j = k.fvar(J_FV);
        let si = succ_of(k, lg, i);
        let sj = succ_of(k, lg, j);
        let ssj = succ_of(k, lg, sj);
        let head = t_app(k, g, &[si, sj]);
        let tail_l = walk(k, &c, antidiag, g, i, ssj);
        let tail_r = walk(k, &c, antidiag, gs, i, sj);
        let h_tail = k.app(ih, sj);
        let refl_head = c.refl(k, head);
        let body = t_app(
            k,
            c.add_congr,
            &[head, head, tail_l, tail_r, refl_head, h_tail],
        );
        let body = lam_over(k, J_FV, c.nat, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, c.nat, body)
    };

    let rec = k.const_(lg.nat_rec, vec![l0]);
    let i = k.fvar(I_FV);
    let j = k.fvar(J_FV);
    let applied = t_app(k, rec, &[motive, minor_zero, minor_succ, i, j]);
    let value = lam_over(k, J_FV, c.nat, applied);
    let value = lam_over(k, I_FV, c.nat, value);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let sj = succ_of(k, lg, j);
        let lhs = walk(k, &c, antidiag, g, i, sj);
        let rhs = walk(k, &c, antidiag, gs, i, j);
        c.eq(k, lhs, rhs)
    };
    let ty = pi_over(k, J_FV, c.nat, concl);
    let ty = pi_over(k, I_FV, c.nat, ty);
    let ty = pi_over(k, G_FV, c.cell, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "antidiagFrom_shift");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.antidiagFrom_succ_last : forall R g n,
/// R.equiv (antidiagFrom R g (succ n) Nat.zero)
///         (R.add (antidiagFrom R (fun a b => g (succ a) b) n Nat.zero)
///                (g Nat.zero (succ n)))`.
///
/// **Peel the LAST cell.** The walk's own recursion peels the FIRST cell
/// (`g (succ n) 0`); this peels the cell the walk visits last, `g 0 (succ n)`.
/// That is the only place the "far" index appears, and it appears as
/// `succ n` — a successor of the induction variable, not a sum — which is
/// exactly why the walk form needs no arithmetic where the subtraction form
/// would need `j + n`.
///
/// `Nat.rec` on `n` with motive `fun n => forall g, …`: the induction
/// hypothesis is consumed at the SHIFTED family `fun a b => g a (succ b)`, so
/// a motive with `g` fixed is unusable. Base is `refl`; the step is
/// shift + IH + one `addAssoc`.
#[allow(clippy::too_many_lines)]
fn declare_antidiag_succ_last(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    shift: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();

    let motive_body = |k: &mut Kernel, c: &RCtx, n: ExprId| {
        let g = k.fvar(G_FV);
        let g1 = shift_first(k, lg, c, g);
        let sn = succ_of(k, lg, n);
        let zero_n = zero_of(k, lg);
        let lhs = walk(k, c, antidiag, g, sn, zero_n);
        let w = walk(k, c, antidiag, g1, n, zero_n);
        let last = t_app(k, g, &[zero_n, sn]);
        let rhs = c.plus(k, w, last);
        let body = c.eq(k, lhs, rhs);
        pi_over(k, G_FV, c.cell, body)
    };
    let motive = {
        let n = k.fvar(M_FV);
        let body = motive_body(k, &c, n);
        lam_over(k, M_FV, c.nat, body)
    };
    let minor_zero = {
        let g = k.fvar(G_FV);
        let zero_n = zero_of(k, lg);
        let one_n = succ_of(k, lg, zero_n);
        let lhs = walk(k, &c, antidiag, g, one_n, zero_n);
        let body = c.refl(k, lhs);
        lam_over(k, G_FV, c.cell, body)
    };
    let minor_succ = {
        let m = k.fvar(M_FV);
        let ih_ty = motive_body(k, &c, m);
        let ih = k.fvar(IH_FV);
        let g = k.fvar(G_FV);

        let zero_n = zero_of(k, lg);
        let one_n = succ_of(k, lg, zero_n);
        let sm = succ_of(k, lg, m);
        let ssm = succ_of(k, lg, sm);

        let gs = shift_second(k, lg, &c, g);
        let g1 = shift_first(k, lg, &c, g);
        let gb = shift_both(k, lg, &c, g);

        let head = t_app(k, g, &[ssm, zero_n]);
        let last = t_app(k, g, &[zero_n, ssm]);
        let w_both = walk(k, &c, antidiag, gb, m, zero_n);

        // a : equiv (W g (succ m) 1) (W gs (succ m) 0)   [the shift lemma]
        let w_g_sm_1 = walk(k, &c, antidiag, g, sm, one_n);
        let w_gs_sm_0 = walk(k, &c, antidiag, gs, sm, zero_n);
        let a = {
            let s = k.const_(shift, vec![]);
            t_app(k, s, &[c.r, g, sm, zero_n])
        };
        // b : ih gs -- equiv (W gs (succ m) 0)
        //                    (add (W gb m 0) (g 0 (succ (succ m))))
        let b = k.app(ih, gs);
        let mid = c.plus(k, w_both, last);
        let tail_chain = c.trans(k, w_g_sm_1, w_gs_sm_0, mid, a, b);

        // left : equiv (add head (W g (succ m) 1)) (add head mid), whose LHS
        // is `W g (succ (succ m)) 0` definitionally.
        let refl_head = c.refl(k, head);
        let left = t_app(
            k,
            c.add_congr,
            &[head, head, w_g_sm_1, mid, refl_head, tail_chain],
        );

        // rr : equiv (W g1 (succ m) 0) (add head (W gb m 0)) -- shift again.
        let w_g1_m_1 = walk(k, &c, antidiag, g1, m, one_n);
        let cshift = {
            let s = k.const_(shift, vec![]);
            t_app(k, s, &[c.r, g1, m, zero_n])
        };
        let refl_head2 = c.refl(k, head);
        let rr = t_app(
            k,
            c.add_congr,
            &[head, head, w_g1_m_1, w_both, refl_head2, cshift],
        );

        let w_g1_sm_0 = walk(k, &c, antidiag, g1, sm, zero_n);
        let add_head_wboth = c.plus(k, head, w_both);
        let refl_last = c.refl(k, last);
        let rrr = t_app(
            k,
            c.add_congr,
            &[w_g1_sm_0, add_head_wboth, last, last, rr, refl_last],
        );

        let target_rhs = c.plus(k, w_g1_sm_0, last);
        let add_hw_last = c.plus(k, add_head_wboth, last);
        let add_head_mid = c.plus(k, head, mid);
        let assoc = t_app(k, c.add_assoc, &[head, w_both, last]);
        let sa = c.symm(k, add_hw_last, add_head_mid, assoc);
        let srrr = c.symm(k, target_rhs, add_hw_last, rrr);

        let lhs_w = walk(k, &c, antidiag, g, ssm, zero_n);
        let step1 = c.trans(k, lhs_w, add_head_mid, add_hw_last, left, sa);
        let body = c.trans(k, lhs_w, add_hw_last, target_rhs, step1, srrr);

        let body = lam_over(k, G_FV, c.cell, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, M_FV, c.nat, body)
    };

    let rec = k.const_(lg.nat_rec, vec![l0]);
    let n = k.fvar(M_FV);
    let g = k.fvar(G_FV);
    let applied = t_app(k, rec, &[motive, minor_zero, minor_succ, n, g]);
    let value = lam_over(k, M_FV, c.nat, applied);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let g1 = shift_first(k, lg, &c, g);
        let sn = succ_of(k, lg, n);
        let zero_n = zero_of(k, lg);
        let lhs = walk(k, &c, antidiag, g, sn, zero_n);
        let w = walk(k, &c, antidiag, g1, n, zero_n);
        let last = t_app(k, g, &[zero_n, sn]);
        let rhs = c.plus(k, w, last);
        c.eq(k, lhs, rhs)
    };
    let ty = pi_over(k, M_FV, c.nat, concl);
    let ty = pi_over(k, G_FV, c.cell, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "antidiagFrom_succ_last");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.antidiagFrom_rev : forall R g n,
/// R.equiv (antidiagFrom R g n Nat.zero)
///         (antidiagFrom R (fun a b => g b a) n Nat.zero)`.
///
/// **The reversal.** Walking the antidiagonal `i + j = n` downward in `i` and
/// walking it downward in `j` sum to the same thing. This is the lemma
/// `mulComm` is, once the cells are transposed by `R.mulComm`.
///
/// `Nat.rec` on `n` with motive `fun n => forall g, …` again. The step reads:
/// the head `g (succ m) 0` plus the shifted tail, whose IH gives the
/// transposed walk; the peel-the-last lemma applied to `gᵀ` produces the very
/// same transposed walk plus the same head, in the other order — so the two
/// sides differ by exactly one `addComm`. The two families `(gᵀ)⁺` and
/// `(g↑)ᵀ` are the same lambda, `fun a b => g b (succ a)`, which is what
/// makes the step close.
#[allow(clippy::too_many_lines)]
fn declare_antidiag_rev(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    shift: NameId,
    succ_last: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();

    let motive_body = |k: &mut Kernel, c: &RCtx, n: ExprId| {
        let g = k.fvar(G_FV);
        let gt = transpose_cells(k, c, g);
        let zero_n = zero_of(k, lg);
        let lhs = walk(k, c, antidiag, g, n, zero_n);
        let rhs = walk(k, c, antidiag, gt, n, zero_n);
        let body = c.eq(k, lhs, rhs);
        pi_over(k, G_FV, c.cell, body)
    };
    let motive = {
        let n = k.fvar(M_FV);
        let body = motive_body(k, &c, n);
        lam_over(k, M_FV, c.nat, body)
    };
    let minor_zero = {
        let g = k.fvar(G_FV);
        let zero_n = zero_of(k, lg);
        let lhs = walk(k, &c, antidiag, g, zero_n, zero_n);
        let body = c.refl(k, lhs);
        lam_over(k, G_FV, c.cell, body)
    };
    let minor_succ = {
        let m = k.fvar(M_FV);
        let ih_ty = motive_body(k, &c, m);
        let ih = k.fvar(IH_FV);
        let g = k.fvar(G_FV);

        let zero_n = zero_of(k, lg);
        let one_n = succ_of(k, lg, zero_n);
        let sm = succ_of(k, lg, m);

        let gs = shift_second(k, lg, &c, g);
        let gt = transpose_cells(k, &c, g);
        // `z := fun a b => g b (succ a)` -- BOTH `(g↑)ᵀ` and `(gᵀ)⁺`.
        let z = {
            let i = k.fvar(I_FV);
            let j = k.fvar(J_FV);
            let si = succ_of(k, lg, i);
            let body = t_app(k, g, &[j, si]);
            let body = lam_over(k, J_FV, c.nat, body);
            lam_over(k, I_FV, c.nat, body)
        };

        let head = t_app(k, g, &[sm, zero_n]);
        let w_g_m_1 = walk(k, &c, antidiag, g, m, one_n);
        let w_gs_m_0 = walk(k, &c, antidiag, gs, m, zero_n);
        let w_z_m_0 = walk(k, &c, antidiag, z, m, zero_n);

        let a = {
            let s = k.const_(shift, vec![]);
            t_app(k, s, &[c.r, g, m, zero_n])
        };
        let b = k.app(ih, gs);
        let tail_chain = c.trans(k, w_g_m_1, w_gs_m_0, w_z_m_0, a, b);
        let refl_head = c.refl(k, head);
        let left = t_app(
            k,
            c.add_congr,
            &[head, head, w_g_m_1, w_z_m_0, refl_head, tail_chain],
        );

        let cc = {
            let s = k.const_(succ_last, vec![]);
            t_app(k, s, &[c.r, gt, m])
        };
        let w_gt_sm_0 = walk(k, &c, antidiag, gt, sm, zero_n);
        let z_head = c.plus(k, w_z_m_0, head);
        let head_z = c.plus(k, head, w_z_m_0);
        let comm = t_app(k, c.add_comm, &[head, w_z_m_0]);

        let lhs_w = walk(k, &c, antidiag, g, sm, zero_n);
        let step1 = c.trans(k, lhs_w, head_z, z_head, left, comm);
        let scc = c.symm(k, w_gt_sm_0, z_head, cc);
        let body = c.trans(k, lhs_w, z_head, w_gt_sm_0, step1, scc);

        let body = lam_over(k, G_FV, c.cell, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, M_FV, c.nat, body)
    };

    let rec = k.const_(lg.nat_rec, vec![l0]);
    let n = k.fvar(M_FV);
    let g = k.fvar(G_FV);
    let applied = t_app(k, rec, &[motive, minor_zero, minor_succ, n, g]);
    let value = lam_over(k, M_FV, c.nat, applied);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let gt = transpose_cells(k, &c, g);
        let zero_n = zero_of(k, lg);
        let lhs = walk(k, &c, antidiag, g, n, zero_n);
        let rhs = walk(k, &c, antidiag, gt, n, zero_n);
        c.eq(k, lhs, rhs)
    };
    let ty = pi_over(k, M_FV, c.nat, concl);
    let ty = pi_over(k, G_FV, c.cell, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "antidiagFrom_rev");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.antidiagFrom_tail_zero : forall R g,
/// (forall i j, R.equiv (g i (succ j)) R.zero) ->
/// forall i j, R.equiv (antidiagFrom R g i (succ j)) R.zero`.
///
/// Every cell the walk visits from a NON-ZERO second index has a non-zero
/// second index, so if the family vanishes off the `j = 0` column the whole
/// tail vanishes. `Nat.rec` on `i` with motive `fun i => forall j, …`.
fn declare_antidiag_tail_zero(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let g = k.fvar(G_FV);

    let hyp_ty = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let sj = succ_of(k, lg, j);
        let cell = t_app(k, g, &[i, sj]);
        let body = c.eq(k, cell, c.zero);
        let body = pi_over(k, J_FV, c.nat, body);
        pi_over(k, I_FV, c.nat, body)
    };
    let h = k.fvar(H_FV);

    let motive_body = |k: &mut Kernel, c: &RCtx, i: ExprId| {
        let j = k.fvar(J_FV);
        let sj = succ_of(k, lg, j);
        let lhs = walk(k, c, antidiag, g, i, sj);
        let body = c.eq(k, lhs, c.zero);
        pi_over(k, J_FV, c.nat, body)
    };
    let motive = {
        let i = k.fvar(I_FV);
        let body = motive_body(k, &c, i);
        lam_over(k, I_FV, c.nat, body)
    };
    let minor_zero = {
        let j = k.fvar(J_FV);
        let zero_n = zero_of(k, lg);
        let body = t_app(k, h, &[zero_n, j]);
        lam_over(k, J_FV, c.nat, body)
    };
    let minor_succ = {
        let i = k.fvar(I_FV);
        let ih_ty = motive_body(k, &c, i);
        let ih = k.fvar(IH_FV);
        let j = k.fvar(J_FV);
        let si = succ_of(k, lg, i);
        let sj = succ_of(k, lg, j);
        let ssj = succ_of(k, lg, sj);
        let head = t_app(k, g, &[si, sj]);
        let tail = walk(k, &c, antidiag, g, i, ssj);
        let h_head = t_app(k, h, &[si, j]);
        let h_tail = k.app(ih, sj);
        let congr = t_app(
            k,
            c.add_congr,
            &[head, c.zero, tail, c.zero, h_head, h_tail],
        );
        let sum = c.plus(k, head, tail);
        let zz = c.plus(k, c.zero, c.zero);
        let az = k.app(c.add_zero, c.zero);
        let body = c.trans(k, sum, zz, c.zero, congr, az);
        let body = lam_over(k, J_FV, c.nat, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, c.nat, body)
    };

    let rec = k.const_(lg.nat_rec, vec![l0]);
    let proof = t_app(k, rec, &[motive, minor_zero, minor_succ]);
    let value = lam_over(k, H_FV, hyp_ty, proof);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let i = k.fvar(I_FV);
        let body = motive_body(k, &c, i);
        pi_over(k, I_FV, c.nat, body)
    };
    let ty = pi_over(k, H_FV, hyp_ty, concl);
    let ty = pi_over(k, G_FV, c.cell, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "antidiagFrom_tail_zero");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.antidiagFrom_head : forall R g,
/// (forall i j, R.equiv (g i (succ j)) R.zero) ->
/// forall n, R.equiv (antidiagFrom R g n Nat.zero) (g n Nat.zero)`.
///
/// **The vanishing-tail collapse.** With the tail gone the whole walk is its
/// first cell. This is the lemma `mulOneR` is, at the family
/// `fun i j => R.mul (p i) (AlgS.Poly.one R j)`, whose off-column cells are
/// `p i * R.zero` (because `AlgS.Poly.one R (succ j)` iota-reduces to
/// `R.zero`) and so vanish by `AlgS.mul_zero`.
fn declare_antidiag_head(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    tail_zero: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let g = k.fvar(G_FV);

    let hyp_ty = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let sj = succ_of(k, lg, j);
        let cell = t_app(k, g, &[i, sj]);
        let body = c.eq(k, cell, c.zero);
        let body = pi_over(k, J_FV, c.nat, body);
        pi_over(k, I_FV, c.nat, body)
    };
    let h = k.fvar(H_FV);

    let motive_body = |k: &mut Kernel, c: &RCtx, n: ExprId| {
        let zero_n = zero_of(k, lg);
        let lhs = walk(k, c, antidiag, g, n, zero_n);
        let rhs = t_app(k, g, &[n, zero_n]);
        c.eq(k, lhs, rhs)
    };
    let motive = {
        let n = k.fvar(M_FV);
        let body = motive_body(k, &c, n);
        lam_over(k, M_FV, c.nat, body)
    };
    let minor_zero = {
        let zero_n = zero_of(k, lg);
        let cell = t_app(k, g, &[zero_n, zero_n]);
        c.refl(k, cell)
    };
    let minor_succ = {
        let m = k.fvar(M_FV);
        let ih_ty = motive_body(k, &c, m);
        let zero_n = zero_of(k, lg);
        let one_n = succ_of(k, lg, zero_n);
        let sm = succ_of(k, lg, m);
        let head = t_app(k, g, &[sm, zero_n]);
        let tail = walk(k, &c, antidiag, g, m, one_n);
        let tz = {
            let t = k.const_(tail_zero, vec![]);
            t_app(k, t, &[c.r, g, h, m, zero_n])
        };
        let refl_head = c.refl(k, head);
        let congr = t_app(k, c.add_congr, &[head, head, tail, c.zero, refl_head, tz]);
        let sum = c.plus(k, head, tail);
        let head_zero = c.plus(k, head, c.zero);
        let az = k.app(c.add_zero, head);
        let body = c.trans(k, sum, head_zero, head, congr, az);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, M_FV, c.nat, body)
    };

    let rec = k.const_(lg.nat_rec, vec![l0]);
    let proof = t_app(k, rec, &[motive, minor_zero, minor_succ]);
    let value = lam_over(k, H_FV, hyp_ty, proof);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let n = k.fvar(M_FV);
        let body = motive_body(k, &c, n);
        pi_over(k, M_FV, c.nat, body)
    };
    let ty = pi_over(k, H_FV, hyp_ty, concl);
    let ty = pi_over(k, G_FV, c.cell, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "antidiagFrom_head");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.antidiagFrom_mul_right : forall R g x i j,
/// R.equiv (R.mul (antidiagFrom R g i j) x)
///         (antidiagFrom R (fun a b => R.mul (g a b) x) i j)`.
///
/// A right factor distributes into every cell of the walk — `distribR`, once
/// per step. `mulAssoc` needs it to move `s 0` inside the inner convolution.
fn declare_antidiag_mul_right(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    antidiag: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let g = k.fvar(G_FV);
    let x = k.fvar(EL_FV);
    let gx = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let cell = t_app(k, g, &[i, j]);
        let body = c.times(k, cell, x);
        let body = lam_over(k, J_FV, c.nat, body);
        lam_over(k, I_FV, c.nat, body)
    };

    let motive_body = |k: &mut Kernel, c: &RCtx, i: ExprId| {
        let j = k.fvar(J_FV);
        let w = walk(k, c, antidiag, g, i, j);
        let lhs = c.times(k, w, x);
        let rhs = walk(k, c, antidiag, gx, i, j);
        let body = c.eq(k, lhs, rhs);
        pi_over(k, J_FV, c.nat, body)
    };
    let motive = {
        let i = k.fvar(I_FV);
        let body = motive_body(k, &c, i);
        lam_over(k, I_FV, c.nat, body)
    };
    let minor_zero = {
        let j = k.fvar(J_FV);
        let zero_n = zero_of(k, lg);
        let cell = t_app(k, g, &[zero_n, j]);
        let lhs = c.times(k, cell, x);
        let body = c.refl(k, lhs);
        lam_over(k, J_FV, c.nat, body)
    };
    let minor_succ = {
        let i = k.fvar(I_FV);
        let ih_ty = motive_body(k, &c, i);
        let ih = k.fvar(IH_FV);
        let j = k.fvar(J_FV);
        let si = succ_of(k, lg, i);
        let sj = succ_of(k, lg, j);
        let head = t_app(k, g, &[si, j]);
        let tail = walk(k, &c, antidiag, g, i, sj);
        let sum = c.plus(k, head, tail);
        let lhs = c.times(k, sum, x);
        let head_x = c.times(k, head, x);
        let tail_x = c.times(k, tail, x);
        let split = c.plus(k, head_x, tail_x);
        let dr = t_app(k, c.distrib_r, &[head, tail, x]);
        let w_gx = walk(k, &c, antidiag, gx, i, sj);
        let h_tail = k.app(ih, sj);
        let refl_head = c.refl(k, head_x);
        let congr = t_app(
            k,
            c.add_congr,
            &[head_x, head_x, tail_x, w_gx, refl_head, h_tail],
        );
        let target = c.plus(k, head_x, w_gx);
        let body = c.trans(k, lhs, split, target, dr, congr);
        let body = lam_over(k, J_FV, c.nat, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, I_FV, c.nat, body)
    };

    let rec = k.const_(lg.nat_rec, vec![l0]);
    let i = k.fvar(I_FV);
    let j = k.fvar(J_FV);
    let applied = t_app(k, rec, &[motive, minor_zero, minor_succ, i, j]);
    let value = lam_over(k, J_FV, c.nat, applied);
    let value = lam_over(k, I_FV, c.nat, value);
    let value = lam_over(k, EL_FV, c.carrier, value);
    let value = lam_over(k, G_FV, c.cell, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let w = walk(k, &c, antidiag, g, i, j);
        let lhs = c.times(k, w, x);
        let rhs = walk(k, &c, antidiag, gx, i, j);
        c.eq(k, lhs, rhs)
    };
    let ty = pi_over(k, J_FV, c.nat, concl);
    let ty = pi_over(k, I_FV, c.nat, ty);
    let ty = pi_over(k, EL_FV, c.carrier, ty);
    let ty = pi_over(k, G_FV, c.cell, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "antidiagFrom_mul_right");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.mul_succ : forall R p q n,
/// R.equiv (AlgS.Poly.mul R p q (succ n))
///         (R.add (R.mul (p (succ n)) (q Nat.zero))
///                (AlgS.Poly.mul R p (fun j => q (succ j)) n))`.
///
/// **The convolution's own recursion.** The walk's `succ` step peels the
/// leading cell `p (succ n) * q 0` and leaves a walk starting one step along
/// the second index; the shift lemma turns that into the convolution of `p`
/// with `q` shifted down. `mulAssoc` runs on this recursion — twice on the
/// left and twice on the right — and nothing else.
fn declare_poly_mul_succ(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    antidiag: NameId,
    shift: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let mul_c = {
        let t = k.const_(names.mul, vec![]);
        k.app(t, c.r)
    };
    let p = k.fvar(P_FV);
    let q = k.fvar(Q_FV);
    let n = k.fvar(M_FV);
    let zero_n = zero_of(k, lg);
    let sn = succ_of(k, lg, n);

    let shq = {
        let j = k.fvar(J_FV);
        let sj = succ_of(k, lg, j);
        let body = k.app(q, sj);
        lam_over(k, J_FV, c.nat, body)
    };
    let p_sn = k.app(p, sn);
    let q0 = k.app(q, zero_n);
    let head = c.times(k, p_sn, q0);
    let cells = mul_cells(k, &c, p, q);
    let one_n = succ_of(k, lg, zero_n);
    let tail_l = walk(k, &c, antidiag, cells, n, one_n);
    let tail_r = {
        let m = app2(k, mul_c, p, shq);
        k.app(m, n)
    };
    let sh = {
        let t = k.const_(shift, vec![]);
        t_app(k, t, &[c.r, cells, n, zero_n])
    };
    let refl_head = c.refl(k, head);
    let value = t_app(k, c.add_congr, &[head, head, tail_l, tail_r, refl_head, sh]);
    let value = lam_over(k, M_FV, c.nat, value);
    let value = lam_over(k, Q_FV, c.poly, value);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let lhs = {
            let m = app2(k, mul_c, p, q);
            k.app(m, sn)
        };
        let rhs = c.plus(k, head, tail_r);
        c.eq(k, lhs, rhs)
    };
    let ty = pi_over(k, M_FV, c.nat, concl);
    let ty = pi_over(k, Q_FV, c.poly, ty);
    let ty = pi_over(k, P_FV, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "mul_succ");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.mulComm : forall R p q,
/// AlgS.Poly.equiv R (AlgS.Poly.mul R p q) (AlgS.Poly.mul R q p)` — the
/// `mulComm` field of `R[X]`.
///
/// Reversal of the walk (`antidiagFrom_rev`) puts the antidiagonal in the
/// other order; `R.mulComm` at each cell turns `p j * q i` into `q i * p j`.
/// Two steps, no induction of its own.
fn declare_poly_mul_comm(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    antidiag: NameId,
    rev: NameId,
    congr: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let equiv_c = {
        let t = k.const_(names.equiv, vec![]);
        k.app(t, c.r)
    };
    let mul_c = {
        let t = k.const_(names.mul, vec![]);
        k.app(t, c.r)
    };
    let p = k.fvar(P_FV);
    let q = k.fvar(Q_FV);
    let n = k.fvar(M_FV);
    let zero_n = zero_of(k, lg);

    let cells = mul_cells(k, &c, p, q);
    let cells_t = transpose_cells(k, &c, cells);
    let cells_qp = mul_cells(k, &c, q, p);

    let lhs = walk(k, &c, antidiag, cells, n, zero_n);
    let mid = walk(k, &c, antidiag, cells_t, n, zero_n);
    let rhs = walk(k, &c, antidiag, cells_qp, n, zero_n);

    let step1 = {
        let t = k.const_(rev, vec![]);
        t_app(k, t, &[c.r, cells, n])
    };
    let cell_hyp = {
        let i = k.fvar(I_FV);
        let j = k.fvar(J_FV);
        let pj = k.app(p, j);
        let qi = k.app(q, i);
        let body = t_app(k, c.mul_comm, &[pj, qi]);
        let body = lam_over(k, J_FV, c.nat, body);
        lam_over(k, I_FV, c.nat, body)
    };
    let step2 = {
        let t = k.const_(congr, vec![]);
        t_app(k, t, &[c.r, cells_t, cells_qp, cell_hyp, n, zero_n])
    };
    let body = c.trans(k, lhs, mid, rhs, step1, step2);
    let value = lam_over(k, M_FV, c.nat, body);
    let value = lam_over(k, Q_FV, c.poly, value);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let l = app2(k, mul_c, p, q);
        let r = app2(k, mul_c, q, p);
        app2(k, equiv_c, l, r)
    };
    let ty = pi_over(k, Q_FV, c.poly, concl);
    let ty = pi_over(k, P_FV, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "mulComm");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.mulOneR : forall R p,
/// AlgS.Poly.equiv R (AlgS.Poly.mul R p (AlgS.Poly.one R)) p`.
///
/// `AlgS.Poly.one R (succ j)` iota-reduces to `R.zero`, so every cell the
/// walk visits after its first is `p i * R.zero`, which `AlgS.mul_zero`
/// kills; `antidiagFrom_head` collapses the walk to `p n * R.one` and
/// `R.mulOneR` finishes.
fn declare_poly_mul_one_r(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    antidiag: NameId,
    head_lemma: NameId,
    deps: PolyDeps,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let equiv_c = {
        let t = k.const_(names.equiv, vec![]);
        k.app(t, c.r)
    };
    let mul_c = {
        let t = k.const_(names.mul, vec![]);
        k.app(t, c.r)
    };
    let one_c = {
        let t = k.const_(names.one, vec![]);
        k.app(t, c.r)
    };
    let p = k.fvar(P_FV);
    let n = k.fvar(M_FV);
    let zero_n = zero_of(k, lg);

    let cells = mul_cells(k, &c, p, one_c);
    // The ring `R` viewed as an `AlgS.Ring`, so `AlgS.mul_zero` applies.
    let r_ring = {
        let t = k.const_(deps.comm_ring_to_ring_s, vec![]);
        k.app(t, c.r)
    };
    let cell_hyp = {
        let i = k.fvar(I_FV);
        let pi = k.app(p, i);
        let mz = k.const_(deps.mul_zero, vec![]);
        // The cell is `p i * AlgS.Poly.one R (succ j)`, and
        // `AlgS.Poly.one R (succ j)` iota-reduces to `R.zero` for EVERY `j` --
        // so the witness does not mention `j` at all.
        let body = t_app(k, mz, &[r_ring, pi]);
        let body = lam_over(k, J_FV, c.nat, body);
        lam_over(k, I_FV, c.nat, body)
    };
    let collapse = {
        let t = k.const_(head_lemma, vec![]);
        t_app(k, t, &[c.r, cells, cell_hyp, n])
    };
    let lhs = walk(k, &c, antidiag, cells, n, zero_n);
    let pn = k.app(p, n);
    let mid = c.times(k, pn, c.one);
    let unit = k.app(c.mul_one_r, pn);
    let body = c.trans(k, lhs, mid, pn, collapse, unit);
    let value = lam_over(k, M_FV, c.nat, body);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let l = app2(k, mul_c, p, one_c);
        app2(k, equiv_c, l, p)
    };
    let ty = pi_over(k, P_FV, c.poly, concl);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "mulOneR");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.mulOneL : forall R p,
/// AlgS.Poly.equiv R (AlgS.Poly.mul R (AlgS.Poly.one R) p) p` — `mulComm`
/// then `mulOneR`, one `equivTrans` at each coefficient.
///
/// The mirror collapse (a family vanishing off the `i = 0` ROW, whose one
/// surviving cell is the LAST the walk visits) is deliberately not proved:
/// commutativity is already available and reduces this side to the other.
fn declare_poly_mul_one_l(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    mul_comm: NameId,
    mul_one_r: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let equiv_c = {
        let t = k.const_(names.equiv, vec![]);
        k.app(t, c.r)
    };
    let mul_c = {
        let t = k.const_(names.mul, vec![]);
        k.app(t, c.r)
    };
    let one_c = {
        let t = k.const_(names.one, vec![]);
        k.app(t, c.r)
    };
    let p = k.fvar(P_FV);
    let n = k.fvar(M_FV);

    let lhs = {
        let m = app2(k, mul_c, one_c, p);
        k.app(m, n)
    };
    let mid = {
        let m = app2(k, mul_c, p, one_c);
        k.app(m, n)
    };
    let pn = k.app(p, n);
    let comm = {
        let t = k.const_(mul_comm, vec![]);
        let e = t_app(k, t, &[c.r, one_c, p]);
        k.app(e, n)
    };
    let unit = {
        let t = k.const_(mul_one_r, vec![]);
        let e = t_app(k, t, &[c.r, p]);
        k.app(e, n)
    };
    let body = c.trans(k, lhs, mid, pn, comm, unit);
    let value = lam_over(k, M_FV, c.nat, body);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let l = app2(k, mul_c, one_c, p);
        app2(k, equiv_c, l, p)
    };
    let ty = pi_over(k, P_FV, c.poly, concl);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "mulOneL");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.mulAssoc : forall R p q s,
/// AlgS.Poly.equiv R (AlgS.Poly.mul R (AlgS.Poly.mul R p q) s)
///                   (AlgS.Poly.mul R p (AlgS.Poly.mul R q s))`.
///
/// **The two-dimensional exchange ADR-1609 sized as "the hard one", done
/// without any three-index machinery.** `Nat.rec` on the coefficient index
/// with motive `fun n => forall p q s, …`, and the whole step is the
/// convolution's own recursion `mul_succ` applied four times:
///
/// ```text
/// ((p·q)·s)(n+1) ~ (p·q)(n+1)·s 0 + ((p·q)·s↑)(n)        [mul_succ]
///                ~ (p(n+1)·q 0 + (p·q↑)(n))·s 0 + (p·(q·s↑))(n)   [mul_succ, IH]
///                ~ (p(n+1)·q 0)·s 0 + (p·q↑)(n)·s 0 + (p·(q·s↑))(n)  [distribR]
/// (p·(q·s))(n+1) ~ p(n+1)·(q·s)(0) + (p·(λj.(q·s)(j+1)))(n)      [mul_succ]
///                ~ p(n+1)·(q 0·s 0) + (p·(λj. q(j+1)·s 0 + (q·s↑)(j)))(n)
///                ~ p(n+1)·(q 0·s 0) + ((p·q↑)(n)·s 0 + (p·(q·s↑))(n)) [distribL]
/// ```
///
/// and the two lines meet under one `R.mulAssoc` plus one `R.addAssoc`. The
/// only walk lemma it needs beyond `mul_succ` is `antidiagFrom_mul_right`,
/// which pulls the scalar `s 0` out of the inner convolution.
#[allow(clippy::too_many_lines)]
fn declare_poly_mul_assoc(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    antidiag: NameId,
    mul_succ: NameId,
    mul_right: NameId,
    congr: NameId,
    mul_congr_poly: NameId,
    distrib_l_poly: NameId,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);
    let l0 = k.level_zero();
    let equiv_c = {
        let t = k.const_(names.equiv, vec![]);
        k.app(t, c.r)
    };
    let mul_c = {
        let t = k.const_(names.mul, vec![]);
        k.app(t, c.r)
    };
    let add_c = {
        let t = k.const_(names.add, vec![]);
        k.app(t, c.r)
    };

    let motive_body = |k: &mut Kernel, c: &RCtx, n: ExprId| {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let s = k.fvar(S_FV);
        let pq = app2(k, mul_c, p, q);
        let qs = app2(k, mul_c, q, s);
        let l = app2(k, mul_c, pq, s);
        let l = k.app(l, n);
        let r = app2(k, mul_c, p, qs);
        let r = k.app(r, n);
        let body = c.eq(k, l, r);
        let body = pi_over(k, S_FV, c.poly, body);
        let body = pi_over(k, Q_FV, c.poly, body);
        pi_over(k, P_FV, c.poly, body)
    };
    let motive = {
        let n = k.fvar(M_FV);
        let body = motive_body(k, &c, n);
        lam_over(k, M_FV, c.nat, body)
    };
    let minor_zero = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let s = k.fvar(S_FV);
        let zero_n = zero_of(k, lg);
        let p0 = k.app(p, zero_n);
        let q0 = k.app(q, zero_n);
        let s0 = k.app(s, zero_n);
        let body = t_app(k, c.mul_assoc, &[p0, q0, s0]);
        let body = lam_over(k, S_FV, c.poly, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let minor_succ = {
        let m = k.fvar(M_FV);
        let ih_ty = motive_body(k, &c, m);
        let ih = k.fvar(IH_FV);
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let s = k.fvar(S_FV);

        let zero_n = zero_of(k, lg);
        let sm = succ_of(k, lg, m);
        let mul_succ_c = k.const_(mul_succ, vec![]);

        let shq = {
            let j = k.fvar(J_FV);
            let sj = succ_of(k, lg, j);
            let body = k.app(q, sj);
            lam_over(k, J_FV, c.nat, body)
        };
        let shs = {
            let j = k.fvar(J_FV);
            let sj = succ_of(k, lg, j);
            let body = k.app(s, sj);
            lam_over(k, J_FV, c.nat, body)
        };

        let pq = app2(k, mul_c, p, q);
        let qs = app2(k, mul_c, q, s);
        let q_shs = app2(k, mul_c, q, shs);

        let p_sm = k.app(p, sm);
        let q0 = k.app(q, zero_n);
        let s0 = k.app(s, zero_n);
        let inner_a = c.times(k, p_sm, q0);
        let big_a = c.times(k, inner_a, s0);
        let q0s0 = c.times(k, q0, s0);
        let big_a2 = c.times(k, p_sm, q0s0);
        let p_shq_m = {
            let e = app2(k, mul_c, p, shq);
            k.app(e, m)
        };
        let big_b = c.times(k, p_shq_m, s0);
        let big_c = {
            let e = app2(k, mul_c, p, q_shs);
            k.app(e, m)
        };

        // ---- the left-hand chain ----
        let lhs_top = {
            let e = app2(k, mul_c, pq, s);
            k.app(e, sm)
        };
        let pq_sm = k.app(pq, sm);
        let pq_sm_s0 = c.times(k, pq_sm, s0);
        let pq_shs_m = {
            let e = app2(k, mul_c, pq, shs);
            k.app(e, m)
        };
        let sum0 = c.plus(k, pq_sm_s0, pq_shs_m);
        let l0t = t_app(k, mul_succ_c, &[c.r, pq, s, m]);
        let l1 = t_app(k, ih, &[p, q, shs]);
        let l2 = t_app(k, mul_succ_c, &[c.r, p, q, m]);
        let a_plus = c.plus(k, inner_a, p_shq_m);
        let refl_s0 = c.refl(k, s0);
        let l3 = t_app(k, c.mul_congr, &[pq_sm, a_plus, s0, s0, l2, refl_s0]);
        let a_plus_s0 = c.times(k, a_plus, s0);
        let l4 = t_app(k, c.distrib_r, &[inner_a, p_shq_m, s0]);
        let ab = c.plus(k, big_a, big_b);
        let l5 = c.trans(k, pq_sm_s0, a_plus_s0, ab, l3, l4);
        let l6 = t_app(k, c.add_congr, &[pq_sm_s0, ab, pq_shs_m, big_c, l5, l1]);
        let ab_c = c.plus(k, ab, big_c);
        let left = c.trans(k, lhs_top, sum0, ab_c, l0t, l6);

        // ---- the right-hand chain ----
        let rhs_top = {
            let e = app2(k, mul_c, p, qs);
            k.app(e, sm)
        };
        let qs0 = k.app(qs, zero_n);
        let p_sm_qs0 = c.times(k, p_sm, qs0);
        let sh_qs = {
            let j = k.fvar(J_FV);
            let sj = succ_of(k, lg, j);
            let body = k.app(qs, sj);
            lam_over(k, J_FV, c.nat, body)
        };
        let p_shqs_m = {
            let e = app2(k, mul_c, p, sh_qs);
            k.app(e, m)
        };
        let sum_r0 = c.plus(k, p_sm_qs0, p_shqs_m);
        let r0 = t_app(k, mul_succ_c, &[c.r, p, qs, m]);

        // `u j := q (succ j) * s 0`, `v := q · s↑`; `λj. (q·s)(j+1) ~ u + v`.
        let u = {
            let j = k.fvar(J_FV);
            let sj = succ_of(k, lg, j);
            let qsj = k.app(q, sj);
            let body = c.times(k, qsj, s0);
            lam_over(k, J_FV, c.nat, body)
        };
        let v = q_shs;
        let uv = app2(k, add_c, u, v);
        let hyp_uv = {
            let j = k.fvar(J_FV);
            let body = t_app(k, mul_succ_c, &[c.r, q, s, j]);
            lam_over(k, J_FV, c.nat, body)
        };
        let refl_p = {
            let n = k.fvar(N_FV);
            let pn = k.app(p, n);
            let body = c.refl(k, pn);
            lam_over(k, N_FV, c.nat, body)
        };
        let r1b = {
            let t = k.const_(mul_congr_poly, vec![]);
            let e = t_app(k, t, &[c.r, p, p, sh_qs, uv, refl_p, hyp_uv]);
            k.app(e, m)
        };
        let p_uv_m = {
            let e = app2(k, mul_c, p, uv);
            k.app(e, m)
        };
        let r1c = {
            let t = k.const_(distrib_l_poly, vec![]);
            let e = t_app(k, t, &[c.r, p, u, v]);
            k.app(e, m)
        };
        let p_u_m = {
            let e = app2(k, mul_c, p, u);
            k.app(e, m)
        };
        let p_u_c = c.plus(k, p_u_m, big_c);

        // `(p·q↑)(m) · s 0 ~ (p·u)(m)`: pull `s 0` into the walk, then
        // reassociate each cell.
        let cells_pshq = mul_cells(k, &c, p, shq);
        let mr = {
            let t = k.const_(mul_right, vec![]);
            t_app(k, t, &[c.r, cells_pshq, s0, m, zero_n])
        };
        let gx1 = {
            let i = k.fvar(I_FV);
            let j = k.fvar(J_FV);
            let sj = succ_of(k, lg, j);
            let pi = k.app(p, i);
            let qsj = k.app(q, sj);
            let inner = c.times(k, pi, qsj);
            let body = c.times(k, inner, s0);
            let body = lam_over(k, J_FV, c.nat, body);
            lam_over(k, I_FV, c.nat, body)
        };
        let gx2 = {
            let i = k.fvar(I_FV);
            let j = k.fvar(J_FV);
            let sj = succ_of(k, lg, j);
            let pi = k.app(p, i);
            let qsj = k.app(q, sj);
            let inner = c.times(k, qsj, s0);
            let body = c.times(k, pi, inner);
            let body = lam_over(k, J_FV, c.nat, body);
            lam_over(k, I_FV, c.nat, body)
        };
        let hyp_assoc = {
            let i = k.fvar(I_FV);
            let j = k.fvar(J_FV);
            let sj = succ_of(k, lg, j);
            let pi = k.app(p, i);
            let qsj = k.app(q, sj);
            let body = t_app(k, c.mul_assoc, &[pi, qsj, s0]);
            let body = lam_over(k, J_FV, c.nat, body);
            lam_over(k, I_FV, c.nat, body)
        };
        let w_gx1 = walk(k, &c, antidiag, gx1, m, zero_n);
        let w_gx2 = walk(k, &c, antidiag, gx2, m, zero_n);
        let cg = {
            let t = k.const_(congr, vec![]);
            t_app(k, t, &[c.r, gx1, gx2, hyp_assoc, m, zero_n])
        };
        let r1d_fwd = c.trans(k, big_b, w_gx1, w_gx2, mr, cg);
        let r1d = c.symm(k, big_b, p_u_m, r1d_fwd);
        let refl_big_c = c.refl(k, big_c);
        let bc = c.plus(k, big_b, big_c);
        let r1e = t_app(
            k,
            c.add_congr,
            &[p_u_m, big_b, big_c, big_c, r1d, refl_big_c],
        );
        let t1 = c.trans(k, p_shqs_m, p_uv_m, p_u_c, r1b, r1c);
        let r1 = c.trans(k, p_shqs_m, p_u_c, bc, t1, r1e);

        let refl_a2 = c.refl(k, big_a2);
        let r2 = t_app(
            k,
            c.add_congr,
            &[p_sm_qs0, big_a2, p_shqs_m, bc, refl_a2, r1],
        );
        let a2_bc = c.plus(k, big_a2, bc);
        let right = c.trans(k, rhs_top, sum_r0, a2_bc, r0, r2);

        // ---- the join ----
        let assoc = t_app(k, c.add_assoc, &[big_a, big_b, big_c]);
        let a_bc = c.plus(k, big_a, bc);
        let step1 = c.trans(k, lhs_top, ab_c, a_bc, left, assoc);
        let ma = t_app(k, c.mul_assoc, &[p_sm, q0, s0]);
        let refl_bc = c.refl(k, bc);
        let cg2 = t_app(k, c.add_congr, &[big_a, big_a2, bc, bc, ma, refl_bc]);
        let step2 = c.trans(k, lhs_top, a_bc, a2_bc, step1, cg2);
        let sright = c.symm(k, rhs_top, a2_bc, right);
        let body = c.trans(k, lhs_top, a2_bc, rhs_top, step2, sright);

        let body = lam_over(k, S_FV, c.poly, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        let body = lam_over(k, P_FV, c.poly, body);
        let body = lam_over(k, IH_FV, ih_ty, body);
        lam_over(k, M_FV, c.nat, body)
    };

    let rec = k.const_(lg.nat_rec, vec![l0]);
    let p = k.fvar(P_FV);
    let q = k.fvar(Q_FV);
    let s = k.fvar(S_FV);
    let n = k.fvar(M_FV);
    let applied = t_app(k, rec, &[motive, minor_zero, minor_succ, n, p, q, s]);
    let value = lam_over(k, M_FV, c.nat, applied);
    let value = lam_over(k, S_FV, c.poly, value);
    let value = lam_over(k, Q_FV, c.poly, value);
    let value = lam_over(k, P_FV, c.poly, value);
    let value = lam_over(k, R_FV, c.ring_ty, value);

    let concl = {
        let pq = app2(k, mul_c, p, q);
        let qs = app2(k, mul_c, q, s);
        let l = app2(k, mul_c, pq, s);
        let r = app2(k, mul_c, p, qs);
        app2(k, equiv_c, l, r)
    };
    let ty = pi_over(k, S_FV, c.poly, concl);
    let ty = pi_over(k, Q_FV, c.poly, ty);
    let ty = pi_over(k, P_FV, c.poly, ty);
    let ty = pi_over(k, R_FV, c.ring_ty, ty);

    let name = k.name_str(poly_ns, "mulAssoc");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Poly.commRing : AlgS.CommRing -> AlgS.CommRing` — **`R[X]` as a
/// commutative ring**, all 23 fields.
///
/// This is the declaration that turns "a polynomial ring structure" into "a
/// polynomial ring": the kernel checks every law of `AlgS.CommRing` at the
/// coefficient function carrier `Nat -> R.carrier`, with `AlgS.Poly.equiv R`
/// as the equality. The additive twelve are `R`'s own fields applied at the
/// index (identically to `AlgS.Poly.commGroup`); the multiplicative four are
/// the theorems above.
#[allow(clippy::too_many_lines)]
fn declare_poly_comm_ring(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    names: &PolyOpNames,
    ring_fields: PolyRingFieldNames,
    poly_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = rctx(k, lg, cr);

    let at_r = |k: &mut Kernel, n: NameId| {
        let t = k.const_(n, vec![]);
        k.app(t, c.r)
    };
    let equiv_c = at_r(k, names.equiv);
    let add_c = at_r(k, names.add);
    let mul_c = at_r(k, names.mul);
    let zero_c = at_r(k, names.zero);
    let one_c = at_r(k, names.one);
    let neg_c = at_r(k, names.neg);
    let mul_congr_c = at_r(k, ring_fields.mul_congr);
    let mul_assoc_c = at_r(k, ring_fields.mul_assoc);
    let mul_one_l_c = at_r(k, ring_fields.mul_one_l);
    let mul_one_r_c = at_r(k, ring_fields.mul_one_r);
    let distrib_l_c = at_r(k, ring_fields.distrib_l);
    let distrib_r_c = at_r(k, ring_fields.distrib_r);
    let mul_comm_c = at_r(k, ring_fields.mul_comm);

    let f_refl = {
        let p = k.fvar(P_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = c.refl(k, pn);
        let body = lam_over(k, N_FV, c.nat, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let f_symm = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let hyp = app2(k, equiv_c, p, q);
        let h = k.fvar(H_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let hn = k.app(h, n);
        let body = c.symm(k, pn, qn, hn);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, H_FV, hyp, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let f_trans = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let s = k.fvar(S_FV);
        let hyp1 = app2(k, equiv_c, p, q);
        let hyp2 = app2(k, equiv_c, q, s);
        let h1 = k.fvar(HP_FV);
        let h2 = k.fvar(HQ_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let sn = k.app(s, n);
        let h1n = k.app(h1, n);
        let h2n = k.app(h2, n);
        let body = c.trans(k, pn, qn, sn, h1n, h2n);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, HQ_FV, hyp2, body);
        let body = lam_over(k, HP_FV, hyp1, body);
        let body = lam_over(k, S_FV, c.poly, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let f_add_congr = {
        let p = k.fvar(P_FV);
        let pp = k.fvar(A_FV);
        let q = k.fvar(Q_FV);
        let qq = k.fvar(B_FV);
        let hyp1 = app2(k, equiv_c, p, pp);
        let hyp2 = app2(k, equiv_c, q, qq);
        let h1 = k.fvar(HP_FV);
        let h2 = k.fvar(HQ_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let ppn = k.app(pp, n);
        let qn = k.app(q, n);
        let qqn = k.app(qq, n);
        let h1n = k.app(h1, n);
        let h2n = k.app(h2, n);
        let body = t_app(k, c.add_congr, &[pn, ppn, qn, qqn, h1n, h2n]);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, HQ_FV, hyp2, body);
        let body = lam_over(k, HP_FV, hyp1, body);
        let body = lam_over(k, B_FV, c.poly, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        let body = lam_over(k, A_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let f_add_assoc = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let s = k.fvar(S_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let sn = k.app(s, n);
        let body = t_app(k, c.add_assoc, &[pn, qn, sn]);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, S_FV, c.poly, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let f_add_comm = {
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let qn = k.app(q, n);
        let body = t_app(k, c.add_comm, &[pn, qn]);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, Q_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let f_add_zero = {
        let p = k.fvar(P_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = k.app(c.add_zero, pn);
        let body = lam_over(k, N_FV, c.nat, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let f_neg_congr = {
        let p = k.fvar(P_FV);
        let pp = k.fvar(A_FV);
        let hyp = app2(k, equiv_c, p, pp);
        let h = k.fvar(H_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let ppn = k.app(pp, n);
        let hn = k.app(h, n);
        let body = t_app(k, c.neg_congr, &[pn, ppn, hn]);
        let body = lam_over(k, N_FV, c.nat, body);
        let body = lam_over(k, H_FV, hyp, body);
        let body = lam_over(k, A_FV, c.poly, body);
        lam_over(k, P_FV, c.poly, body)
    };
    let f_neg_add = {
        let p = k.fvar(P_FV);
        let n = k.fvar(N_FV);
        let pn = k.app(p, n);
        let body = k.app(c.neg_add, pn);
        let body = lam_over(k, N_FV, c.nat, body);
        lam_over(k, P_FV, c.poly, body)
    };

    let value = mk_instance(
        k,
        cr,
        &[
            c.poly,
            equiv_c,
            f_refl,
            f_symm,
            f_trans,
            zero_c,
            one_c,
            add_c,
            mul_c,
            f_add_congr,
            mul_congr_c,
            f_add_assoc,
            f_add_comm,
            f_add_zero,
            mul_assoc_c,
            mul_one_l_c,
            mul_one_r_c,
            distrib_l_c,
            distrib_r_c,
            neg_c,
            f_neg_congr,
            f_neg_add,
            mul_comm_c,
        ],
    );
    let value = lam_over(k, R_FV, c.ring_ty, value);
    let ty = arrow(k, c.ring_ty, c.ring_ty);

    let name = k.name_str(poly_ns, "commRing");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

/// The names of the coefficient-function operations, threaded into the
/// instance and the theorems that use them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PolyOpNames {
    pub equiv: NameId,
    pub add: NameId,
    pub zero: NameId,
    pub neg: NameId,
    pub one: NameId,
    pub smul: NameId,
    pub mul: NameId,
}

/// ADR-1618: the two `structures_setoid` results `AlgS.Poly.mulOneR` needs.
///
/// `AlgS.mul_zero` is stated over `AlgS.Ring`, so it reaches an
/// `AlgS.CommRing` through the prefix projection `AlgS.CommRing.toRingS`.
/// Both are declared by `declare_structures_s_extra`, which runs before this
/// module at every call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PolyDeps {
    /// `AlgS.CommRing.toRingS`.
    pub comm_ring_to_ring_s: NameId,
    /// `AlgS.mul_zero : forall (R : AlgS.Ring) a, R.equiv (R.mul a R.zero) R.zero`.
    pub mul_zero: NameId,
}

/// The eight `AlgS.Poly.*` theorems that ARE the multiplicative fields of
/// `AlgS.Poly.commRing`, gathered so the instance builder cannot pick up a
/// name by accident.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PolyRingFieldNames {
    mul_congr: NameId,
    mul_assoc: NameId,
    mul_one_l: NameId,
    mul_one_r: NameId,
    distrib_l: NameId,
    distrib_r: NameId,
    mul_comm: NameId,
}

/// Every `AlgS.Poly.*` name this module declares, plus `AlgS.add_add_add_comm`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PolyNames {
    pub add_add_add_comm: NameId,
    pub ops: PolyOpNames,
    pub comm_group: NameId,
    pub antidiag_from: NameId,
    pub antidiag_from_congr: NameId,
    pub antidiag_from_add: NameId,
    pub mul_congr: NameId,
    pub distrib_l: NameId,
    pub distrib_r: NameId,
    // -- ADR-1618: the reindexing lemmas and the four fields they close. --
    /// `AlgS.Poly.antidiagFrom_shift`.
    pub antidiag_from_shift: NameId,
    /// `AlgS.Poly.antidiagFrom_succ_last`.
    pub antidiag_from_succ_last: NameId,
    /// `AlgS.Poly.antidiagFrom_rev` — the reversal.
    pub antidiag_from_rev: NameId,
    /// `AlgS.Poly.antidiagFrom_tail_zero`.
    pub antidiag_from_tail_zero: NameId,
    /// `AlgS.Poly.antidiagFrom_head` — the vanishing-tail collapse.
    pub antidiag_from_head: NameId,
    /// `AlgS.Poly.antidiagFrom_mul_right`.
    pub antidiag_from_mul_right: NameId,
    /// `AlgS.Poly.mul_succ` — the convolution's own recursion.
    pub mul_succ: NameId,
    /// `AlgS.Poly.mulComm`.
    pub mul_comm: NameId,
    /// `AlgS.Poly.mulOneR`.
    pub mul_one_r: NameId,
    /// `AlgS.Poly.mulOneL`.
    pub mul_one_l: NameId,
    /// `AlgS.Poly.mulAssoc` — the two-dimensional exchange.
    pub mul_assoc: NameId,
    /// **`AlgS.Poly.commRing`** — `R[X]` as a full 23-field `AlgS.CommRing`.
    pub comm_ring: NameId,
}

/// `#[cfg(test)]` because these names are deliberately NOT threaded into
/// `NatPrelude` (see the call site in `nat_prelude.rs`), so the only consumer
/// of the roster is the suite below; a plain `--lib` build would flag it dead.
#[cfg(test)]
impl PolyNames {
    /// The twenty-seven declarations, in dependency order. Derived from the
    /// struct so a renamed or dropped declaration breaks a test rather than
    /// the test's idea of what exists.
    #[must_use]
    pub fn all(&self) -> [NameId; 27] {
        [
            self.add_add_add_comm,
            self.ops.equiv,
            self.ops.add,
            self.ops.zero,
            self.ops.neg,
            self.ops.one,
            self.ops.smul,
            self.comm_group,
            self.antidiag_from,
            self.ops.mul,
            self.antidiag_from_congr,
            self.antidiag_from_add,
            self.mul_congr,
            self.distrib_l,
            self.distrib_r,
            self.antidiag_from_shift,
            self.antidiag_from_succ_last,
            self.antidiag_from_rev,
            self.antidiag_from_tail_zero,
            self.antidiag_from_head,
            self.antidiag_from_mul_right,
            self.mul_succ,
            self.mul_comm,
            self.mul_one_r,
            self.mul_one_l,
            self.mul_assoc,
            self.comm_ring,
        ]
    }
}

/// Declare `AlgS.add_add_add_comm` and the whole `AlgS.Poly.*` namespace.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means
/// [`Kernel::add_declaration`] **refused** a proof term.
pub(crate) fn declare_poly_setoid(
    k: &mut Kernel,
    lg: &LogicPrelude,
    comm_ring: &RecordNames,
    comm_group: &RecordNames,
    deps: PolyDeps,
    algs_p: NameId,
) -> Result<PolyNames, KernelError> {
    let poly_ns = k.name_str(algs_p, "Poly");

    let add_add_add_comm = declare_add_add_add_comm(k, lg, comm_ring, algs_p)?;

    let equiv = declare_poly_equiv(k, lg, comm_ring, poly_ns)?;
    let add = declare_poly_add(k, lg, comm_ring, poly_ns)?;
    let zero = declare_poly_zero(k, lg, comm_ring, poly_ns)?;
    let neg = declare_poly_neg(k, lg, comm_ring, poly_ns)?;
    let one = declare_poly_one(k, lg, comm_ring, poly_ns)?;
    let smul = declare_poly_smul(k, lg, comm_ring, poly_ns)?;
    // `mul` is not declared yet; the instance below uses only the additive
    // operations, so the placeholder is never read.
    let ops = PolyOpNames {
        equiv,
        add,
        zero,
        neg,
        one,
        smul,
        mul: equiv,
    };
    let comm_group_name = declare_poly_comm_group(k, lg, comm_ring, comm_group, &ops, poly_ns)?;

    let antidiag_from = declare_antidiag_from(k, lg, comm_ring, poly_ns)?;
    let mul = declare_poly_mul(k, lg, comm_ring, antidiag_from, poly_ns)?;
    let ops = PolyOpNames { mul, ..ops };

    let antidiag_from_congr = declare_antidiag_congr(k, lg, comm_ring, antidiag_from, poly_ns)?;
    let antidiag_from_add =
        declare_antidiag_add(k, lg, comm_ring, antidiag_from, add_add_add_comm, poly_ns)?;
    let mul_congr = declare_poly_mul_congr(k, lg, comm_ring, &ops, antidiag_from_congr, poly_ns)?;
    let distrib_l = declare_poly_distrib_l(k, lg, comm_ring, &ops, antidiag_from_add, poly_ns)?;
    let distrib_r = declare_poly_distrib_r(k, lg, comm_ring, &ops, antidiag_from_add, poly_ns)?;

    // -- ADR-1618: the reindexing lemmas, the four remaining ring fields, and
    // the `AlgS.CommRing` instance they complete. --
    let antidiag_from_shift = declare_antidiag_shift(k, lg, comm_ring, antidiag_from, poly_ns)?;
    let antidiag_from_succ_last = declare_antidiag_succ_last(
        k,
        lg,
        comm_ring,
        antidiag_from,
        antidiag_from_shift,
        poly_ns,
    )?;
    let antidiag_from_rev = declare_antidiag_rev(
        k,
        lg,
        comm_ring,
        antidiag_from,
        antidiag_from_shift,
        antidiag_from_succ_last,
        poly_ns,
    )?;
    let antidiag_from_tail_zero =
        declare_antidiag_tail_zero(k, lg, comm_ring, antidiag_from, poly_ns)?;
    let antidiag_from_head = declare_antidiag_head(
        k,
        lg,
        comm_ring,
        antidiag_from,
        antidiag_from_tail_zero,
        poly_ns,
    )?;
    let antidiag_from_mul_right =
        declare_antidiag_mul_right(k, lg, comm_ring, antidiag_from, poly_ns)?;
    let mul_succ = declare_poly_mul_succ(
        k,
        lg,
        comm_ring,
        &ops,
        antidiag_from,
        antidiag_from_shift,
        poly_ns,
    )?;
    let mul_comm = declare_poly_mul_comm(
        k,
        lg,
        comm_ring,
        &ops,
        antidiag_from,
        antidiag_from_rev,
        antidiag_from_congr,
        poly_ns,
    )?;
    let mul_one_r = declare_poly_mul_one_r(
        k,
        lg,
        comm_ring,
        &ops,
        antidiag_from,
        antidiag_from_head,
        deps,
        poly_ns,
    )?;
    let mul_one_l = declare_poly_mul_one_l(k, lg, comm_ring, &ops, mul_comm, mul_one_r, poly_ns)?;
    let mul_assoc = declare_poly_mul_assoc(
        k,
        lg,
        comm_ring,
        &ops,
        antidiag_from,
        mul_succ,
        antidiag_from_mul_right,
        antidiag_from_congr,
        mul_congr,
        distrib_l,
        poly_ns,
    )?;
    let comm_ring_name = declare_poly_comm_ring(
        k,
        lg,
        comm_ring,
        &ops,
        PolyRingFieldNames {
            mul_congr,
            mul_assoc,
            mul_one_l,
            mul_one_r,
            distrib_l,
            distrib_r,
            mul_comm,
        },
        poly_ns,
    )?;

    Ok(PolyNames {
        add_add_add_comm,
        ops,
        comm_group: comm_group_name,
        antidiag_from,
        antidiag_from_congr,
        antidiag_from_add,
        mul_congr,
        distrib_l,
        distrib_r,
        antidiag_from_shift,
        antidiag_from_succ_last,
        antidiag_from_rev,
        antidiag_from_tail_zero,
        antidiag_from_head,
        antidiag_from_mul_right,
        mul_succ,
        mul_comm,
        mul_one_r,
        mul_one_l,
        mul_assoc,
        comm_ring: comm_ring_name,
    })
}

// ---------------------------------------------------------------------------
// Tests. Every assertion reads the KERNEL -- `add_declaration`'s verdict,
// `Kernel::axiom_footprint`, or `Kernel::def_eq` -- never a rendered name or
// a comment in this file.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod poly_setoid_tests {
    use super::*;
    use crate::build_logic_prelude;
    use crate::nat_prelude::structures as algeq;
    use crate::nat_prelude::structures_setoid::{
        StructuresSNames, StructuresSRecordNames, declare_structures_s_all,
        declare_structures_s_extra, intern_structures_s_names,
    };

    struct Fixture {
        lg: LogicPrelude,
        st: StructuresSRecordNames,
        p: StructuresSNames,
        poly: PolyNames,
    }

    /// The whole dependency set is `logic`, the `Alg`/`AlgS` records and
    /// `declare_structures_s_extra` -- still no `Nat` arithmetic, which is
    /// the build position this module was written for and the claim ADR-1618
    /// measures. The `Alg` spine appears only because
    /// `declare_structures_s_extra` (which declares `AlgS.mul_zero`, needed
    /// by `mulOneR`) also declares the nine `ofAlg` projections.
    fn build(k: &mut Kernel) -> Fixture {
        let lg = build_logic_prelude(k).expect("logic prelude must build");
        let alg_p = algeq::intern_structures_names(k);
        let alg_st = algeq::declare_structures_all(k, &alg_p, &lg).expect("Alg spine builds");
        let p = intern_structures_s_names(k);
        let st = declare_structures_s_all(k, &p, &lg).expect("AlgS spine builds");
        let extra = declare_structures_s_extra(k, &lg, &p, &st, &alg_p, &alg_st)
            .expect("AlgS extras must admit");
        let poly = declare_poly_setoid(
            k,
            &lg,
            &st.comm_ring,
            &st.comm_group,
            PolyDeps {
                comm_ring_to_ring_s: extra.comm_ring_to_ring_s,
                mul_zero: extra.mul_zero,
            },
            p.algs,
        )
        .expect("the polynomial ring over an abstract AlgS.CommRing must admit");
        Fixture { lg, st, p, poly }
    }

    /// `Nat` numeral as `succ^n zero`. Unary, and every use here is at 0, 1 or
    /// 2 -- the magnitudes stay small on purpose (CLAUDE.md, prelude cost).
    fn numeral(k: &mut Kernel, lg: &LogicPrelude, n: usize) -> ExprId {
        let mut e = k.const_(lg.nat_zero, vec![]);
        for _ in 0..n {
            let s = k.const_(lg.nat_succ, vec![]);
            e = k.app(s, e);
        }
        e
    }

    #[test]
    fn the_polynomial_ring_declarations_admit_by_the_setoid_route() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.poly.all() {
            assert!(
                k.environment().get(name).is_some(),
                "declaration missing from the environment"
            );
        }
    }

    /// **The headline claim.** Read from `Kernel::axiom_footprint`, the
    /// transitive trusted-base closure of the checked declaration.
    #[test]
    fn the_polynomial_ring_is_axiom_free() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.poly.all() {
            let footprint = k.axiom_footprint(name);
            assert!(
                footprint.is_empty(),
                "axiom footprint must be empty, got {} entries",
                footprint.len()
            );
        }
    }

    /// `AlgS.Poly.commGroup` is a `Definition` producing a genuine
    /// `AlgS.CommGroup` VALUE -- so the kernel checked all sixteen fields --
    /// and the walk lemmas are `Theorem`s, so the kernel checked their proof
    /// terms. A stub cannot pass this.
    #[test]
    fn the_additive_group_is_a_checked_comm_group_value() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let cg = k
            .environment()
            .get(f.poly.comm_group)
            .expect("commGroup must exist")
            .clone();
        assert!(
            matches!(cg, Declaration::Definition { .. }),
            "AlgS.Poly.commGroup must be a Definition producing an AlgS.CommGroup"
        );
        for name in [
            f.poly.antidiag_from_congr,
            f.poly.antidiag_from_add,
            f.poly.mul_congr,
            f.poly.distrib_l,
            f.poly.distrib_r,
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

    /// Every declaration's type renders, and every one of them is stated over
    /// an ABSTRACT `AlgS.CommRing` — which is the claim W2-9 makes, and the
    /// one a concrete-carrier development would fail. Prints the types so a
    /// referee can read them out of the suite rather than out of a doc.
    #[test]
    fn the_polynomial_ring_types_render_over_an_abstract_comm_ring() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.poly.all() {
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
                rendered.contains("AlgS.CommRing"),
                "every AlgS.Poly declaration must be stated over an abstract \
                 AlgS.CommRing, got: {rendered}"
            );
        }
    }

    /// **Evaluation test for `AlgS.Poly.one`.** The carrier is abstract, so
    /// "evaluate at concrete arguments" means: reduce the definition at
    /// concrete INDICES and compare the result to the hand-written term. The
    /// negative twins differ in one small term (`one` for `zero`) and must
    /// NOT hold, so the test cannot pass by `def_eq` being vacuously true.
    #[test]
    fn poly_one_computes_one_at_index_zero_and_zero_after() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let c = rctx(&mut k, &f.lg, &f.st.comm_ring);
        let one_c = k.const_(f.poly.ops.one, vec![]);

        for (idx, expected, wrong) in [
            (0_usize, c.one, c.zero),
            (1, c.zero, c.one),
            (2, c.zero, c.one),
        ] {
            let n = numeral(&mut k, &f.lg, idx);
            let lhs = t_app(&mut k, one_c, &[c.r, n]);
            assert!(
                k.def_eq(lhs, expected),
                "AlgS.Poly.one R {idx} must reduce to the expected coefficient"
            );
            assert!(
                !k.def_eq(lhs, wrong),
                "AlgS.Poly.one R {idx} must NOT reduce to the other coefficient"
            );
        }
    }

    /// **Evaluation test for `AlgS.Poly.mul`** -- the one that pins the
    /// convolution ORDER, which is the property a reversed or off-by-one walk
    /// would break. At index 1 the correct value is `p 1 * q 0 + p 0 * q 1`;
    /// the negative twin swaps the two summands, a change of exactly two
    /// subterms, and must be refused.
    #[test]
    fn poly_mul_computes_the_convolution_in_the_declared_order() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let c = rctx(&mut k, &f.lg, &f.st.comm_ring);
        let mul_c = k.const_(f.poly.ops.mul, vec![]);
        let p = k.fvar(P_FV);
        let q = k.fvar(Q_FV);

        // n = 0: p 0 * q 0.
        {
            let n = numeral(&mut k, &f.lg, 0);
            let lhs = t_app(&mut k, mul_c, &[c.r, p, q, n]);
            let i0 = numeral(&mut k, &f.lg, 0);
            let p0 = k.app(p, i0);
            let q0 = k.app(q, i0);
            let rhs = c.times(&mut k, p0, q0);
            assert!(k.def_eq(lhs, rhs), "(p*q) 0 must be p 0 * q 0");
            let wrong = c.times(&mut k, q0, p0);
            assert!(
                !k.def_eq(lhs, wrong),
                "(p*q) 0 must NOT be q 0 * p 0 -- the ring is abstract, so the \
                 factors are not interchangeable definitionally"
            );
        }

        // n = 1: (p 1 * q 0) + (p 0 * q 1), in that order.
        {
            let n = numeral(&mut k, &f.lg, 1);
            let lhs = t_app(&mut k, mul_c, &[c.r, p, q, n]);
            let i0 = numeral(&mut k, &f.lg, 0);
            let i1 = numeral(&mut k, &f.lg, 1);
            let p0 = k.app(p, i0);
            let p1 = k.app(p, i1);
            let q0 = k.app(q, i0);
            let q1 = k.app(q, i1);
            let t10 = c.times(&mut k, p1, q0);
            let t01 = c.times(&mut k, p0, q1);
            let rhs = c.plus(&mut k, t10, t01);
            assert!(k.def_eq(lhs, rhs), "(p*q) 1 must be p1*q0 + p0*q1");
            let swapped = c.plus(&mut k, t01, t10);
            assert!(
                !k.def_eq(lhs, swapped),
                "(p*q) 1 must NOT be p0*q1 + p1*q0 -- the walk's order is part \
                 of the definition and a reversed walk would pass otherwise"
            );
        }

        // n = 2: (p 2 * q 0) + ((p 1 * q 1) + (p 0 * q 2)) -- right-nested,
        // which is what the walk's `add head tail` shape produces.
        {
            let n = numeral(&mut k, &f.lg, 2);
            let lhs = t_app(&mut k, mul_c, &[c.r, p, q, n]);
            let i0 = numeral(&mut k, &f.lg, 0);
            let i1 = numeral(&mut k, &f.lg, 1);
            let i2 = numeral(&mut k, &f.lg, 2);
            let p0 = k.app(p, i0);
            let p1 = k.app(p, i1);
            let p2 = k.app(p, i2);
            let q0 = k.app(q, i0);
            let q1 = k.app(q, i1);
            let q2 = k.app(q, i2);
            let t20 = c.times(&mut k, p2, q0);
            let t11 = c.times(&mut k, p1, q1);
            let t02 = c.times(&mut k, p0, q2);
            let tail = c.plus(&mut k, t11, t02);
            let rhs = c.plus(&mut k, t20, tail);
            assert!(
                k.def_eq(lhs, rhs),
                "(p*q) 2 must be p2*q0 + (p1*q1 + p0*q2)"
            );
            let left_nested = {
                let head = c.plus(&mut k, t20, t11);
                c.plus(&mut k, head, t02)
            };
            assert!(
                !k.def_eq(lhs, left_nested),
                "(p*q) 2 must NOT be (p2*q0 + p1*q1) + p0*q2 -- addition is \
                 abstract here, so the nesting is observable"
            );
        }
    }

    /// **Negative control for the additive instance.** Rebuild
    /// `AlgS.Poly.commGroup` from its own selectors, swapping ONE field:
    /// slot 11 (`identL`, `equiv (add zero p) p`) gets slot 12's proof
    /// (`identR`, `equiv (add p zero) p`). The two differ in one subterm and
    /// the kernel must refuse the swapped instance.
    ///
    /// The POSITIVE TWIN in the same test is the identical reconstruction
    /// with slot 11 left alone, which must be ACCEPTED -- without it the
    /// refusal would be evidence that the reconstruction technique is broken,
    /// not that `identL` is load-bearing.
    #[test]
    fn the_additive_instance_is_rejected_when_identl_is_supplied_by_identr() {
        use crate::nat_prelude::structures_setoid::idx::comm_group::{COMM, IDENT_L, IDENT_R};
        let mut k = Kernel::new();
        let f = build(&mut k);
        let c = rctx(&mut k, &f.lg, &f.st.comm_ring);

        let rebuild = |k: &mut Kernel, swap: bool| -> ExprId {
            let cg_const = k.const_(f.poly.comm_group, vec![]);
            let inst = k.app(cg_const, c.r);
            let mut args = Vec::with_capacity(COMM + 1);
            for i in 0..=COMM {
                let source = if swap && i == IDENT_L { IDENT_R } else { i };
                args.push(sel(k, &f.st.comm_group, source, inst));
            }
            let v = mk_instance(k, &f.st.comm_group, &args);
            lam_over(k, R_FV, c.ring_ty, v)
        };
        let good = rebuild(&mut k, false);
        let bad = rebuild(&mut k, true);
        let ty = {
            let cg_ty = k.const_(f.st.comm_group.ind, vec![]);
            arrow(&mut k, c.ring_ty, cg_ty)
        };

        // Positive twin: the honest reconstruction must admit.
        let good_name = k.name_str(f.p.algs, "polyCommGroupRebuiltControl");
        assert!(
            k.add_declaration(Declaration::Definition {
                name: good_name,
                uparams: vec![],
                ty,
                value: good,
                hint: ReducibilityHint::Regular(1),
            })
            .is_ok(),
            "the field-by-field reconstruction itself must type-check -- \
             otherwise the refusal below says nothing about identL"
        );

        // The mutant: identL supplied by identR.
        let bad_name = k.name_str(f.p.algs, "polyCommGroupIdentLSwapped");
        assert!(
            k.add_declaration(Declaration::Definition {
                name: bad_name,
                uparams: vec![],
                ty,
                value: bad,
                hint: ReducibilityHint::Regular(1),
            })
            .is_err(),
            "supplying identR's proof for identL must be REFUSED: `equiv (add \
             zero p) p` and `equiv (add p zero) p` are different propositions \
             over an abstract carrier, and the derivation through addComm is \
             what makes the honest field type-check"
        );
    }

    /// **Negative control for `AlgS.add_add_add_comm`.** The admitted proof
    /// term is reused verbatim against a conclusion in which the exchange is
    /// simply not performed (`(a+b)+(c+d) ~ (a+b)+(c+d)`). The kernel must
    /// refuse it, which is what makes the five-step chain load-bearing rather
    /// than decorative.
    #[test]
    fn the_middle_four_exchange_is_rejected_without_the_exchange() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let c = rctx(&mut k, &f.lg, &f.st.comm_ring);

        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let cc = k.fvar(C_FV);
        let d = k.fvar(D_FV);
        let ab = c.plus(&mut k, a, b);
        let cd = c.plus(&mut k, cc, d);
        let lhs = c.plus(&mut k, ab, cd);

        // The honest theorem's own proof term, taken from the environment.
        let value = match k
            .environment()
            .get(f.poly.add_add_add_comm)
            .expect("add_add_add_comm must exist")
        {
            Declaration::Theorem { value, .. } => *value,
            other => panic!("expected a Theorem, got {other:?}"),
        };

        // The mutated conclusion: no exchange at all.
        let concl = c.eq(&mut k, lhs, lhs);
        let ty = pi_over(&mut k, D_FV, c.carrier, concl);
        let ty = pi_over(&mut k, C_FV, c.carrier, ty);
        let ty = pi_over(&mut k, B_FV, c.carrier, ty);
        let ty = pi_over(&mut k, A_FV, c.carrier, ty);
        let ty = pi_over(&mut k, R_FV, c.ring_ty, ty);

        let name = k.name_str(f.p.algs, "addAddAddCommNoExchange");
        assert!(
            k.add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .is_err(),
            "the exchange proof must NOT check against the reflexive statement"
        );
    }
}
