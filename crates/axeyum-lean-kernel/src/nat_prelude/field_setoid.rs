//! `AlgS.Field.*` — ADR-1627, roadmap W3-2: a **constructive** field over the
//! setoid spine, with an apartness relation as positive data, and the
//! multiplicative inverse stated **existentially** rather than as a function.
//!
//! # Why the inverse is an `Exists` and not a field of type
//! `(x : α) → apart x zero → α`
//!
//! That functional shape is the one the brief for this lane proposed, and it
//! is the one `Alg.Field` (the `Eq` spine) approximates with a *total* `inv`
//! plus `mulInv : ∀ a, ¬(a = 0) → a · a⁻¹ = 1`. **`CReal` cannot instantiate
//! the functional shape**, and the reason is recorded verbatim in
//! `creal/inverse.rs`:
//!
//! ```text
//! CReal.inv : (x : CReal) → (k : Nat) → CReal.PosBound x k → CReal
//! ```
//!
//! The **modulus `k` is data**. `CReal.Apart x zero` is
//! `Or (lt x zero) (lt zero x)` — a `Prop` — and `CReal.pos_bound_of_lt`
//! delivers the modulus only inside an `Exists`, which is also a `Prop`. So
//! neither the sign nor the modulus can be eliminated out of an apartness
//! witness into a `CReal`-valued definition, and
//! `inv : (x : α) → apart x zero → α` is **undefinable at `CReal`**. That is
//! not a gap in `creal`; `CReal.no_total_inverse` proves the total form is
//! impossible, and the partial functional form is blocked by
//! large elimination.
//!
//! The existential form
//!
//! ```text
//! mulInvEx : ∀ a, apart a zero → ∃ b, equiv (mul a b) one
//! ```
//!
//! is a `Prop`, so `CReal` discharges it by `Or`-elimination into a `Prop`
//! goal followed by `Exists`-elimination of the modulus — both legal — and
//! **every consumer of a field's inverse in this library is proving a `Prop`
//! anyway**, so nothing is lost: `AlgS.Field.mul_left_cancel` and
//! `AlgS.VectorSpace.solve_smul` both open the existential and never need the
//! inverse as a term. This is also the standard definition in constructive
//! algebra (Bishop; Mines–Richman–Ruitenburg): a field is a ring with a
//! tight apartness in which every element apart from `0` is invertible.
//!
//! # Why tightness is a predicate and not a field
//!
//! `apartTight : ∀ a b, ¬(apart a b) → equiv a b` is **not** one of the
//! record's fields; it is [`FieldNames::is_tight`], a separate `Prop` over an
//! `AlgS.Field`. The measurement behind that split: `ℚ` proves it in three
//! lines from `Rat.lt_trichotomy`, and `CReal` **cannot prove it from
//! anything in the tree** — `creal.rs`'s own doc block calls it Markov's
//! principle, which is *wrong* (Markov is the converse, `¬equiv → apart`),
//! but the constructive proof it does need — `¬(lt x y) → le y x`, i.e. a
//! single-index introduction rule for `CReal.lt` — is not among `CReal`'s
//! 400-odd order lemmas. Making tightness a field would have made `CReal` not
//! a field, for a property no theorem below uses. ADR-1627 records this.
//!
//! # Field layout (29 fields; `MAX_FIELDS` is 32)
//!
//! | idx | field | shape |
//! |---|---|---|
//! | 0–22 | `AlgS.CommRing`'s own 23, verbatim | |
//! | 23 | `apart` | `α → α → Prop` |
//! | 24 | `apartSymm` | `∀ a b, apart a b → apart b a` |
//! | 25 | `apartCotrans` | `∀ a b, apart a b → ∀ c, Or (apart a c) (apart c b)` |
//! | 26 | `apartCompat` | `∀ a b, equiv a b → apart a b → False` |
//! | 27 | `mulInvEx` | `∀ a, apart a zero → ∃ b, equiv (mul a b) one` |
//! | 28 | `oneApartZero` | `apart one zero` |
//!
//! **Irreflexivity is derived, not assumed** ([`FieldNames::apart_irrefl`]):
//! `apartCompat a a (equivRefl a)` is it. The setoid-compatibility field
//! `apartCompat` is strictly stronger than irreflexivity and is what makes
//! the two congruence directions provable — `apart` congruence follows from
//! cotransitivity plus compatibility and needs no extra field, which
//! `Alg.*`'s `Eq` spine would get free and the setoid spine here recovers for
//! one field rather than two.
//!
//! # What is declared
//!
//! | name | kind | what it is |
//! |---|---|---|
//! | `AlgS.Field` | inductive | the record above |
//! | `AlgS.Field.toCommRing` | definition | forget the apartness and the inverse |
//! | `AlgS.Field.ofCommRing` | definition | build one from a ring and six proofs |
//! | `AlgS.Field.IsTight` | definition | `∀ a b, ¬(apart a b) → equiv a b` |
//! | `AlgS.Field.apart_irrefl` | theorem | `apart a a → False` |
//! | `AlgS.Field.apart_left_congr` | theorem | `equiv a a' → apart a b → apart a' b` |
//! | `AlgS.Field.apart_right_congr` | theorem | `equiv b b' → apart a b → apart a b'` |
//! | `AlgS.Field.inv_unique` | theorem | two inverses of one element are equivalent |
//! | `AlgS.Field.mul_left_cancel` | theorem | `a # 0 → a·x ~ a·y → x ~ y` |

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

use super::structures::{
    FieldKind, FieldSpec, RecordNames, app2, arrow, declare_record, lam_over, pi_over, sel,
};
use super::structures_setoid::{comm_ring_fields_for_field_s, idx};

// ---------------------------------------------------------------------------
// Free-variable blocks. The FIELD-SPEC builders reuse `structures.rs`'s own
// 9_9xx band shape but at 9_95x so a spec of this module and a spec of that
// one can be nested inside one type without capture; the PROOF builders use
// the 24_xxx band, disjoint from `module_setoid`'s 23_xxx.
// ---------------------------------------------------------------------------

const S_A: u64 = 9_950;
const S_B: u64 = 9_951;
const S_C: u64 = 9_952;

const F_FV: u64 = 24_000;
const R_FV: u64 = 24_001;
const AP_FV: u64 = 24_002;
const A_FV: u64 = 24_010;
const APR_FV: u64 = 24_011;
const B_FV: u64 = 24_012;
const BPR_FV: u64 = 24_013;
const X_FV: u64 = 24_014;
const Y_FV: u64 = 24_015;
const H1_FV: u64 = 24_020;
const H2_FV: u64 = 24_021;
const SCRATCH_FV: u64 = 24_030;
/// One fvar per `ofCommRing` hypothesis, indexed by the field it discharges.
const OFC_HYP_BASE: u64 = 24_100;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

// ---------------------------------------------------------------------------
// The six new field specs.
// ---------------------------------------------------------------------------

/// `carrier -> carrier -> Prop` — apartness as DATA, never as `Not (equiv …)`.
fn apart_field_s(carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "apart",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[carrier_idx];
            let l0 = k.level_zero();
            let prop = k.sort(l0);
            let inner = arrow(k, a, prop);
            arrow(k, a, inner)
        }),
    }
}

/// `forall a b, apart a b -> apart b a`.
fn apart_symm_field_s(carrier_idx: usize, apart_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "apartSymm",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let ap = vals[apart_idx];
            let va = k.fvar(S_A);
            let vb = k.fvar(S_B);
            let hab = app2(k, ap, va, vb);
            let hba = app2(k, ap, vb, va);
            let inner = arrow(k, hab, hba);
            let t = pi_over(k, S_B, a_ty, inner);
            pi_over(k, S_A, a_ty, t)
        }),
    }
}

/// `forall a b, apart a b -> forall c, Or (apart a c) (apart c b)` — Bishop's
/// cotransitivity, in the argument order `CReal.apart_cotrans` already has.
fn apart_cotrans_field_s(carrier_idx: usize, apart_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "apartCotrans",
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let ap = vals[apart_idx];
            let va = k.fvar(S_A);
            let vb = k.fvar(S_B);
            let vc = k.fvar(S_C);
            let hab = app2(k, ap, va, vb);
            let hac = app2(k, ap, va, vc);
            let hcb = app2(k, ap, vc, vb);
            let or_c = k.const_(lg.or, vec![]);
            let disj = app2(k, or_c, hac, hcb);
            let inner = pi_over(k, S_C, a_ty, disj);
            let inner = arrow(k, hab, inner);
            let t = pi_over(k, S_B, a_ty, inner);
            pi_over(k, S_A, a_ty, t)
        }),
    }
}

/// `forall a b, equiv a b -> apart a b -> False` — setoid compatibility.
/// Strictly stronger than irreflexivity, which it derives.
fn apart_compat_field_s(carrier_idx: usize, equiv_idx: usize, apart_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "apartCompat",
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let eqv = vals[equiv_idx];
            let ap = vals[apart_idx];
            let va = k.fvar(S_A);
            let vb = k.fvar(S_B);
            let heq = app2(k, eqv, va, vb);
            let hap = app2(k, ap, va, vb);
            let false_ = k.const_(lg.false_, vec![]);
            let inner = arrow(k, hap, false_);
            let inner = arrow(k, heq, inner);
            let t = pi_over(k, S_B, a_ty, inner);
            pi_over(k, S_A, a_ty, t)
        }),
    }
}

/// `forall a, apart a zero -> Exists carrier (fun b => equiv (mul a b) one)`.
fn mul_inv_ex_field_s(
    carrier_idx: usize,
    equiv_idx: usize,
    zero_idx: usize,
    one_idx: usize,
    mul_idx: usize,
    apart_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: "mulInvEx",
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let eqv = vals[equiv_idx];
            let zero = vals[zero_idx];
            let one = vals[one_idx];
            let mul = vals[mul_idx];
            let ap = vals[apart_idx];
            let va = k.fvar(S_A);
            let hyp = app2(k, ap, va, zero);
            let vb = k.fvar(S_B);
            let prod = app2(k, mul, va, vb);
            let body = app2(k, eqv, prod, one);
            let pred = lam_over(k, S_B, a_ty, body);
            let ex = k.const_(lg.exists_, vec![l1]);
            let concl = app2(k, ex, a_ty, pred);
            let inner = arrow(k, hyp, concl);
            pi_over(k, S_A, a_ty, inner)
        }),
    }
}

/// `apart one zero` — the **non-vacuity** witness. Without it every apartness
/// law above holds of the relation that separates nothing, and the record
/// would admit the zero ring.
fn one_apart_zero_field_s(zero_idx: usize, one_idx: usize, apart_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "oneApartZero",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let zero = vals[zero_idx];
            let one = vals[one_idx];
            let ap = vals[apart_idx];
            app2(k, ap, one, zero)
        }),
    }
}

/// `AlgS.CommRing`'s 23 fields plus the six above.
fn field_fields_s() -> Vec<FieldSpec> {
    use idx::comm_ring as r;
    let mut f = comm_ring_fields_for_field_s();
    debug_assert_eq!(f.len(), 23, "AlgS.CommRing must have 23 fields");
    f.push(apart_field_s(r::CARRIER)); // 23
    f.push(apart_symm_field_s(r::CARRIER, ix::APART)); // 24
    f.push(apart_cotrans_field_s(r::CARRIER, ix::APART)); // 25
    f.push(apart_compat_field_s(r::CARRIER, r::EQUIV, ix::APART)); // 26
    f.push(mul_inv_ex_field_s(
        r::CARRIER,
        r::EQUIV,
        r::ZERO,
        r::ONE,
        r::MUL,
        ix::APART,
    )); // 27
    f.push(one_apart_zero_field_s(r::ZERO, r::ONE, ix::APART)); // 28
    f
}

/// Field indices for `AlgS.Field`, continuing
/// [`super::structures_setoid::idx::comm_ring`]'s numbering.
pub mod ix {
    pub use super::super::structures_setoid::idx::comm_ring::*;
    pub const APART: usize = 23;
    pub const APART_SYMM: usize = 24;
    pub const APART_COTRANS: usize = 25;
    pub const APART_COMPAT: usize = 26;
    pub const MUL_INV_EX: usize = 27;
    pub const ONE_APART_ZERO: usize = 28;
    /// The record's field count, pinned here so a consumer never counts.
    pub const FIELD_COUNT: usize = 29;
}

// ---------------------------------------------------------------------------
// The selector bundle used by every proof below.
// ---------------------------------------------------------------------------

struct FCtx {
    f: ExprId,
    field_ty: ExprId,
    carrier: ExprId,
    equiv: ExprId,
    refl: ExprId,
    symm: ExprId,
    trans: ExprId,
    zero: ExprId,
    one: ExprId,
    mul: ExprId,
    mul_congr: ExprId,
    mul_assoc: ExprId,
    mul_one_l: ExprId,
    mul_one_r: ExprId,
    mul_comm: ExprId,
    apart: ExprId,
    apart_symm: ExprId,
    apart_cotrans: ExprId,
    apart_compat: ExprId,
    mul_inv_ex: ExprId,
}

fn fctx(k: &mut Kernel, fr: &RecordNames) -> FCtx {
    let field_ty = k.const_(fr.ind, vec![]);
    let f = k.fvar(F_FV);
    FCtx {
        f,
        field_ty,
        carrier: sel(k, fr, ix::CARRIER, f),
        equiv: sel(k, fr, ix::EQUIV, f),
        refl: sel(k, fr, ix::EQUIV_REFL, f),
        symm: sel(k, fr, ix::EQUIV_SYMM, f),
        trans: sel(k, fr, ix::EQUIV_TRANS, f),
        zero: sel(k, fr, ix::ZERO, f),
        one: sel(k, fr, ix::ONE, f),
        mul: sel(k, fr, ix::MUL, f),
        mul_congr: sel(k, fr, ix::MUL_CONGR, f),
        mul_assoc: sel(k, fr, ix::MUL_ASSOC, f),
        mul_one_l: sel(k, fr, ix::MUL_ONE_L, f),
        mul_one_r: sel(k, fr, ix::MUL_ONE_R, f),
        mul_comm: sel(k, fr, ix::MUL_COMM, f),
        apart: sel(k, fr, ix::APART, f),
        apart_symm: sel(k, fr, ix::APART_SYMM, f),
        apart_cotrans: sel(k, fr, ix::APART_COTRANS, f),
        apart_compat: sel(k, fr, ix::APART_COMPAT, f),
        mul_inv_ex: sel(k, fr, ix::MUL_INV_EX, f),
    }
}

impl FCtx {
    fn eqv(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.equiv, a, b)
    }
    fn apt(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.apart, a, b)
    }
    fn times(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.mul, a, b)
    }
    fn tr(
        &self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        t_app(k, self.trans, &[a, b, c, h1, h2])
    }
    fn sy(&self, k: &mut Kernel, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        t_app(k, self.symm, &[a, b, h])
    }
    fn rf(&self, k: &mut Kernel, a: ExprId) -> ExprId {
        k.app(self.refl, a)
    }
    /// `mulCongr a a' b b' h1 h2 : equiv (mul a b) (mul a' b')`.
    fn mcongr(
        &self,
        k: &mut Kernel,
        a: ExprId,
        ap: ExprId,
        b: ExprId,
        bp: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        t_app(k, self.mul_congr, &[a, ap, b, bp, h1, h2])
    }
    fn close_pi(&self, k: &mut Kernel, body: ExprId) -> ExprId {
        pi_over(k, F_FV, self.field_ty, body)
    }
    fn close_lam(&self, k: &mut Kernel, body: ExprId) -> ExprId {
        lam_over(k, F_FV, self.field_ty, body)
    }
}

// ---------------------------------------------------------------------------
// `toCommRing` / `ofCommRing`.
// ---------------------------------------------------------------------------

/// `AlgS.Field.toCommRing : AlgS.Field -> AlgS.CommRing` — the forgetful
/// projection, 23 selectors and nothing else. FREE, because the field record's
/// first 23 fields are `AlgS.CommRing`'s own `FieldSpec` closures verbatim.
fn declare_to_comm_ring(
    k: &mut Kernel,
    fr: &RecordNames,
    cr: &RecordNames,
    field_ns: NameId,
) -> Result<NameId, KernelError> {
    let field_ty = k.const_(fr.ind, vec![]);
    let comm_ring_ty = k.const_(cr.ind, vec![]);
    let f = k.fvar(F_FV);
    let args: Vec<ExprId> = (0..23).map(|i| sel(k, fr, i, f)).collect();
    let mk = k.const_(cr.mk, vec![]);
    let body = t_app(k, mk, &args);
    let value = lam_over(k, F_FV, field_ty, body);
    let ty = arrow(k, field_ty, comm_ring_ty);

    let name = k.name_str(field_ns, "toCommRing");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Field.ofCommRing : Pi (R : AlgS.CommRing) (apart : …), <five laws> ->
/// AlgS.Field` — the constructor an INSTANCE calls, so an instance supplies a
/// ring it already has plus six proofs and never re-states 23 ring laws.
///
/// The hypothesis types are built by calling the SAME `FieldSpec` closures the
/// record is declared from, with `vals` the `AlgS.CommRing` selectors at `R`
/// — so they cannot drift from the record's own field types.
fn declare_of_comm_ring(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fr: &RecordNames,
    cr: &RecordNames,
    l1: crate::level::LevelId,
    field_ns: NameId,
) -> Result<NameId, KernelError> {
    let specs = field_fields_s();
    let comm_ring_ty = k.const_(cr.ind, vec![]);
    let field_ty = k.const_(fr.ind, vec![]);
    let r = k.fvar(R_FV);

    let mut vals: Vec<ExprId> = (0..23).map(|i| sel(k, cr, i, r)).collect();

    let apart_ty = (specs[ix::APART].build)(k, lg, l1, &vals);
    vals.push(k.fvar(AP_FV));

    let mut hyps: Vec<(u64, ExprId)> = Vec::with_capacity(5);
    for i in ix::APART_SYMM..ix::FIELD_COUNT {
        let ty = (specs[i].build)(k, lg, l1, &vals);
        let fv = OFC_HYP_BASE + i as u64;
        hyps.push((fv, ty));
        vals.push(k.fvar(fv));
    }

    let mk = k.const_(fr.mk, vec![]);
    let mut value = t_app(k, mk, &vals);
    for (fv, ty) in hyps.iter().rev() {
        value = lam_over(k, *fv, *ty, value);
    }
    value = lam_over(k, AP_FV, apart_ty, value);
    value = lam_over(k, R_FV, comm_ring_ty, value);

    let mut ty = field_ty;
    for (fv, hty) in hyps.iter().rev() {
        ty = pi_over(k, *fv, *hty, ty);
    }
    ty = pi_over(k, AP_FV, apart_ty, ty);
    ty = pi_over(k, R_FV, comm_ring_ty, ty);

    let name = k.name_str(field_ns, "ofCommRing");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Field.IsTight : AlgS.Field -> Prop :=
/// fun F => forall a b, Not (F.apart a b) -> F.equiv a b`.
///
/// A predicate, not a field — see the module doc. `ℚ` satisfies it; whether
/// `CReal` does is open (ADR-1627 §4).
fn declare_is_tight(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fr: &RecordNames,
    field_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = fctx(k, fr);
    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let hap = c.apt(k, a, b);
    let not_c = k.const_(lg.not, vec![]);
    let nap = k.app(not_c, hap);
    let concl = c.eqv(k, a, b);
    let body = arrow(k, nap, concl);
    let body = pi_over(k, B_FV, c.carrier, body);
    let body = pi_over(k, A_FV, c.carrier, body);
    let value = c.close_lam(k, body);
    let ty = c.close_pi(k, prop);

    let name = k.name_str(field_ns, "IsTight");
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
// Theorems.
// ---------------------------------------------------------------------------

/// `AlgS.Field.apart_irrefl : forall (F : AlgS.Field) (a : F.carrier),
/// F.apart a a -> False`. One `apartCompat` at `equivRefl`.
fn declare_apart_irrefl(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fr: &RecordNames,
    field_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = fctx(k, fr);
    let a = k.fvar(A_FV);
    let hap_ty = c.apt(k, a, a);
    let h = k.fvar(H1_FV);
    let refl_a = c.rf(k, a);
    let proof = t_app(k, c.apart_compat, &[a, a, refl_a, h]);

    let value = lam_over(k, H1_FV, hap_ty, proof);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = c.close_lam(k, value);

    let false_ = k.const_(lg.false_, vec![]);
    let ty = arrow(k, hap_ty, false_);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(field_ns, "apart_irrefl");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Field.apart_left_congr : forall F a a' b, F.equiv a a' ->
/// F.apart a b -> F.apart a' b`.
///
/// **This is why `apartCompat` is a field and irreflexivity is not.**
/// Cotransitivity at `c := a'` gives `apart a a' ∨ apart a' b`; the left
/// disjunct is refuted by `apartCompat` against the hypothesis `equiv a a'`,
/// so `Or.resolve_left` returns the right one. With only irreflexivity the
/// left disjunct is not refutable and this theorem does not follow.
fn declare_apart_left_congr(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fr: &RecordNames,
    field_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = fctx(k, fr);
    let a = k.fvar(A_FV);
    let ap = k.fvar(APR_FV);
    let b = k.fvar(B_FV);
    let heq_ty = c.eqv(k, a, ap);
    let hap_ty = c.apt(k, a, b);
    let heq = k.fvar(H1_FV);
    let hap = k.fvar(H2_FV);

    let left = c.apt(k, a, ap);
    let right = c.apt(k, ap, b);
    let cot = t_app(k, c.apart_cotrans, &[a, b, hap, ap]);
    let refute = {
        let hl = k.fvar(SCRATCH_FV);
        let body = t_app(k, c.apart_compat, &[a, ap, heq, hl]);
        lam_over(k, SCRATCH_FV, left, body)
    };
    let resolve = k.const_(lg.or_resolve_left, vec![]);
    let proof = t_app(k, resolve, &[left, right, cot, refute]);

    let value = lam_over(k, H2_FV, hap_ty, proof);
    let value = lam_over(k, H1_FV, heq_ty, value);
    let value = lam_over(k, B_FV, c.carrier, value);
    let value = lam_over(k, APR_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = c.close_lam(k, value);

    let ty = arrow(k, hap_ty, right);
    let ty = arrow(k, heq_ty, ty);
    let ty = pi_over(k, B_FV, c.carrier, ty);
    let ty = pi_over(k, APR_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(field_ns, "apart_left_congr");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Field.apart_right_congr : forall F a b b', F.equiv b b' ->
/// F.apart a b -> F.apart a b'`. [`declare_apart_left_congr`] between two
/// `apartSymm`s.
fn declare_apart_right_congr(
    k: &mut Kernel,
    fr: &RecordNames,
    left_congr: NameId,
    field_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = fctx(k, fr);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let bp = k.fvar(BPR_FV);
    let heq_ty = c.eqv(k, b, bp);
    let hap_ty = c.apt(k, a, b);
    let heq = k.fvar(H1_FV);
    let hap = k.fvar(H2_FV);

    let flipped = t_app(k, c.apart_symm, &[a, b, hap]); // apart b a
    let moved = {
        let t = k.const_(left_congr, vec![]);
        t_app(k, t, &[c.f, b, bp, a, heq, flipped]) // apart b' a
    };
    let proof = t_app(k, c.apart_symm, &[bp, a, moved]); // apart a b'

    let value = lam_over(k, H2_FV, hap_ty, proof);
    let value = lam_over(k, H1_FV, heq_ty, value);
    let value = lam_over(k, BPR_FV, c.carrier, value);
    let value = lam_over(k, B_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = c.close_lam(k, value);

    let concl = c.apt(k, a, bp);
    let ty = arrow(k, hap_ty, concl);
    let ty = arrow(k, heq_ty, ty);
    let ty = pi_over(k, BPR_FV, c.carrier, ty);
    let ty = pi_over(k, B_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(field_ns, "apart_right_congr");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Field.inv_unique : forall F a x y, F.equiv (F.mul a x) F.one ->
/// F.equiv (F.mul a y) F.one -> F.equiv x y`.
///
/// `x ~ 1·x ~ (y·a)·x ~ y·(a·x) ~ y·1 ~ ... ~ y`. Uses no apartness at all —
/// it is a `CommMonoid` fact, restated here because the field record does not
/// project to `AlgS.CommMonoid` (no inheritance in this spine).
fn declare_inv_unique(
    k: &mut Kernel,
    fr: &RecordNames,
    field_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = fctx(k, fr);
    let a = k.fvar(A_FV);
    let x = k.fvar(X_FV);
    let y = k.fvar(Y_FV);
    let ax = c.times(k, a, x);
    let ay = c.times(k, a, y);
    let h1_ty = c.eqv(k, ax, c.one);
    let h2_ty = c.eqv(k, ay, c.one);
    let h1 = k.fvar(H1_FV);
    let h2 = k.fvar(H2_FV);

    // `x ~ y` by cancelling `a`, given both products are `one`.
    let proof = mul_cancel_core(k, &c, a, x, y, h1, h2);

    let value = lam_over(k, H2_FV, h2_ty, proof);
    let value = lam_over(k, H1_FV, h1_ty, value);
    let value = lam_over(k, Y_FV, c.carrier, value);
    let value = lam_over(k, X_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = c.close_lam(k, value);

    let concl = c.eqv(k, x, y);
    let ty = arrow(k, h2_ty, concl);
    let ty = arrow(k, h1_ty, ty);
    let ty = pi_over(k, Y_FV, c.carrier, ty);
    let ty = pi_over(k, X_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(field_ns, "inv_unique");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// From `h1 : equiv (mul a x) one` and `h2 : equiv (mul a y) one`, build
/// `equiv x y`:
/// `x ~ 1·x ~ (y·a)·x ~ y·(a·x) ~ y·1 ~ 1·y ~ y` — with `y·a ~ 1` obtained
/// from `h2` through `mulComm`.
fn mul_cancel_core(
    k: &mut Kernel,
    c: &FCtx,
    a: ExprId,
    x: ExprId,
    y: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let ya = c.times(k, y, a);
    let ay = c.times(k, a, y);
    let ax = c.times(k, a, x);
    // s2 : equiv (y·a) one
    let comm = t_app(k, c.mul_comm, &[y, a]); // equiv (y·a) (a·y)
    let s2 = c.tr(k, ya, ay, c.one, comm, h2);
    let s3 = c.sy(k, ya, c.one, s2); // equiv one (y·a)

    let one_x = c.times(k, c.one, x);
    let ya_x = c.times(k, ya, x);
    let y_ax = c.times(k, y, ax);
    let y_one = c.times(k, y, c.one);

    let p0 = t_app(k, c.mul_one_l, &[x]); // equiv (1·x) x
    let p0s = c.sy(k, one_x, x, p0); // equiv x (1·x)
    let rx = c.rf(k, x);
    let p1 = c.mcongr(k, c.one, ya, x, x, s3, rx); // equiv (1·x) ((y·a)·x)
    let p2 = t_app(k, c.mul_assoc, &[y, a, x]); // equiv ((y·a)·x) (y·(a·x))
    let ry = c.rf(k, y);
    let p3 = c.mcongr(k, y, y, ax, c.one, ry, h1); // equiv (y·(a·x)) (y·1)
    let p4 = t_app(k, c.mul_one_r, &[y]); // equiv (y·1) y

    let t3 = c.tr(k, y_ax, y_one, y, p3, p4);
    let t2 = c.tr(k, ya_x, y_ax, y, p2, t3);
    let t1 = c.tr(k, one_x, ya_x, y, p1, t2);
    c.tr(k, x, one_x, y, p0s, t1)
}

/// `AlgS.Field.mul_left_cancel : forall F a x y, F.apart a F.zero ->
/// F.equiv (F.mul a x) (F.mul a y) -> F.equiv x y`.
///
/// **The theorem the field exists for.** `mulInvEx` is opened by
/// `Exists.rec` into the `Prop` goal — which is exactly why the inverse can be
/// existential — and the witness `b` cancels:
/// `x ~ 1·x ~ (b·a)·x ~ b·(a·x) ~ b·(a·y) ~ (b·a)·y ~ 1·y ~ y`.
fn declare_mul_left_cancel(
    k: &mut Kernel,
    lg: &LogicPrelude,
    fr: &RecordNames,
    l1: crate::level::LevelId,
    field_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = fctx(k, fr);
    let a = k.fvar(A_FV);
    let x = k.fvar(X_FV);
    let y = k.fvar(Y_FV);
    let hap_ty = c.apt(k, a, c.zero);
    let ax = c.times(k, a, x);
    let ay = c.times(k, a, y);
    let heq_ty = c.eqv(k, ax, ay);
    let hap = k.fvar(H1_FV);
    let heq = k.fvar(H2_FV);
    let goal = c.eqv(k, x, y);

    // pred := fun b => equiv (mul a b) one
    let pred = {
        let b = k.fvar(B_FV);
        let ab = c.times(k, a, b);
        let body = c.eqv(k, ab, c.one);
        lam_over(k, B_FV, c.carrier, body)
    };
    let ex = k.const_(lg.exists_, vec![l1]);
    let ex_ty = app2(k, ex, c.carrier, pred);
    let motive = lam_over(k, SCRATCH_FV, ex_ty, goal);
    let witness = t_app(k, c.mul_inv_ex, &[a, hap]);

    let minor = {
        let b = k.fvar(B_FV);
        let ab = c.times(k, a, b);
        let hb_ty = c.eqv(k, ab, c.one);
        let hb = k.fvar(OFC_HYP_BASE);
        let body = cancel_with_inverse(k, &c, a, b, x, y, hb, heq);
        let inner = lam_over(k, OFC_HYP_BASE, hb_ty, body);
        lam_over(k, B_FV, c.carrier, inner)
    };
    let rec = k.const_(lg.exists_rec, vec![l1]);
    let proof = t_app(k, rec, &[c.carrier, pred, motive, minor, witness]);

    let value = lam_over(k, H2_FV, heq_ty, proof);
    let value = lam_over(k, H1_FV, hap_ty, value);
    let value = lam_over(k, Y_FV, c.carrier, value);
    let value = lam_over(k, X_FV, c.carrier, value);
    let value = lam_over(k, A_FV, c.carrier, value);
    let value = c.close_lam(k, value);

    let ty = arrow(k, heq_ty, goal);
    let ty = arrow(k, hap_ty, ty);
    let ty = pi_over(k, Y_FV, c.carrier, ty);
    let ty = pi_over(k, X_FV, c.carrier, ty);
    let ty = pi_over(k, A_FV, c.carrier, ty);
    let ty = c.close_pi(k, ty);

    let name = k.name_str(field_ns, "mul_left_cancel");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// The seven-step chain `x ~ 1·x ~ (b·a)·x ~ b·(a·x) ~ b·(a·y) ~ (b·a)·y ~
/// 1·y ~ y`, given `hb : equiv (mul a b) one` and `heq : equiv (mul a x)
/// (mul a y)`.
#[allow(clippy::too_many_arguments)]
fn cancel_with_inverse(
    k: &mut Kernel,
    c: &FCtx,
    a: ExprId,
    b: ExprId,
    x: ExprId,
    y: ExprId,
    hb: ExprId,
    heq: ExprId,
) -> ExprId {
    let ba = c.times(k, b, a);
    let ab = c.times(k, a, b);
    let ax = c.times(k, a, x);
    let ay = c.times(k, a, y);
    let comm = t_app(k, c.mul_comm, &[b, a]); // equiv (b·a) (a·b)
    let s2 = c.tr(k, ba, ab, c.one, comm, hb); // equiv (b·a) one
    let s3 = c.sy(k, ba, c.one, s2); // equiv one (b·a)

    let one_x = c.times(k, c.one, x);
    let ba_x = c.times(k, ba, x);
    let b_ax = c.times(k, b, ax);
    let b_ay = c.times(k, b, ay);
    let ba_y = c.times(k, ba, y);
    let one_y = c.times(k, c.one, y);

    let rx = c.rf(k, x);
    let ry = c.rf(k, y);
    let rb = c.rf(k, b);

    let p0 = t_app(k, c.mul_one_l, &[x]); // equiv (1·x) x
    let p0s = c.sy(k, one_x, x, p0); // equiv x (1·x)
    let p1 = c.mcongr(k, c.one, ba, x, x, s3, rx); // equiv (1·x) ((b·a)·x)
    let p2 = t_app(k, c.mul_assoc, &[b, a, x]); // equiv ((b·a)·x) (b·(a·x))
    let p3 = c.mcongr(k, b, b, ax, ay, rb, heq); // equiv (b·(a·x)) (b·(a·y))
    let p4 = {
        let assoc = t_app(k, c.mul_assoc, &[b, a, y]); // equiv ((b·a)·y) (b·(a·y))
        c.sy(k, ba_y, b_ay, assoc) // equiv (b·(a·y)) ((b·a)·y)
    };
    let p5 = c.mcongr(k, ba, c.one, y, y, s2, ry); // equiv ((b·a)·y) (1·y)
    let p6 = t_app(k, c.mul_one_l, &[y]); // equiv (1·y) y

    let t5 = c.tr(k, ba_y, one_y, y, p5, p6);
    let t4 = c.tr(k, b_ay, ba_y, y, p4, t5);
    let t3 = c.tr(k, b_ax, b_ay, y, p3, t4);
    let t2 = c.tr(k, ba_x, b_ax, y, p2, t3);
    let t1 = c.tr(k, one_x, ba_x, y, p1, t2);
    c.tr(k, x, one_x, y, p0s, t1)
}

/// `AlgS.mul_neg_right : forall (R : AlgS.CommRing) (a b : R.carrier),
/// R.equiv (R.mul a (R.neg b)) (R.neg (R.mul a b))`.
///
/// **A `CommRing` fact, declared here rather than in `structures_setoid`**,
/// and the reason is operational: `structures_setoid.rs` is a shared file
/// several lanes append to, and adding a spec into
/// `declare_structures_s_extra`'s middle is a merge hazard this lane does not
/// need to take. It is here because the `CReal` field instance is its only
/// consumer: `CReal` has `neg_mul_neg` (squares only) and no `mul_neg`, so
/// the NEGATIVE branch of `mulInvEx` -- the one that turns `a < 0` into
/// `0 < -a` and pushes the inverse back through a sign -- cannot be closed
/// without it.
///
/// Three steps off `AlgS.mul_neg_one` at `AlgS.CommRing.toRingS R`:
/// `a*(-b) ~ a*(b*(-1)) ~ (a*b)*(-1) ~ -(a*b)`.
fn declare_mul_neg_right(
    k: &mut Kernel,
    cr: &RecordNames,
    deps: FieldDeps,
    algs: NameId,
) -> Result<NameId, KernelError> {
    use idx::comm_ring as r;
    let ring_ty = k.const_(cr.ind, vec![]);
    let rv = k.fvar(R_FV);
    let carrier = sel(k, cr, r::CARRIER, rv);
    let equiv = sel(k, cr, r::EQUIV, rv);
    let refl = sel(k, cr, r::EQUIV_REFL, rv);
    let symm = sel(k, cr, r::EQUIV_SYMM, rv);
    let trans = sel(k, cr, r::EQUIV_TRANS, rv);
    let one = sel(k, cr, r::ONE, rv);
    let mul = sel(k, cr, r::MUL, rv);
    let neg = sel(k, cr, r::NEG, rv);
    let mul_congr = sel(k, cr, r::MUL_CONGR, rv);
    let mul_assoc = sel(k, cr, r::MUL_ASSOC, rv);

    // `mul_neg_one` lives over `AlgS.Ring`; `toRingS R`'s selectors iota-reduce
    // to `R`'s own, so no transport term is written.
    let ring_s = {
        let t = k.const_(deps.comm_ring_to_ring_s, vec![]);
        k.app(t, rv)
    };
    let mno = {
        let t = k.const_(deps.mul_neg_one, vec![]);
        k.app(t, ring_s)
    };

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let neg_one = k.app(neg, one);
    let neg_b = k.app(neg, b);
    let ab = app2(k, mul, a, b);
    let a_negb = app2(k, mul, a, neg_b);
    let b_negone = app2(k, mul, b, neg_one);
    let a_b_negone = app2(k, mul, a, b_negone);
    let ab_negone = app2(k, mul, ab, neg_one);
    let neg_ab = k.app(neg, ab);

    let e1 = k.app(mno, b); // equiv (b*(-1)) (-b)
    let e1s = t_app(k, symm, &[b_negone, neg_b, e1]); // (-b) ~ b*(-1)
    let ra = k.app(refl, a);
    let s1 = t_app(k, mul_congr, &[a, a, neg_b, b_negone, ra, e1s]);
    let assoc = t_app(k, mul_assoc, &[a, b, neg_one]); // (a*b)*(-1) ~ a*(b*(-1))
    let s2 = t_app(k, symm, &[ab_negone, a_b_negone, assoc]);
    let s3 = k.app(mno, ab); // (a*b)*(-1) ~ -(a*b)
    let tail = t_app(k, trans, &[a_b_negone, ab_negone, neg_ab, s2, s3]);
    let proof = t_app(k, trans, &[a_negb, a_b_negone, neg_ab, s1, tail]);

    let value = lam_over(k, B_FV, carrier, proof);
    let value = lam_over(k, A_FV, carrier, value);
    let value = lam_over(k, R_FV, ring_ty, value);

    let concl = app2(k, equiv, a_negb, neg_ab);
    let ty = pi_over(k, B_FV, carrier, concl);
    let ty = pi_over(k, A_FV, carrier, ty);
    let ty = pi_over(k, R_FV, ring_ty, ty);

    let name = k.name_str(algs, "mul_neg_right");
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

/// Every name this module declares, plus the record itself.
///
/// `#[allow(dead_code)]` for the reason `ModuleNames`'s own `all` carries
/// `#[cfg(test)]`: these names are deliberately NOT threaded into
/// `NatPrelude` (see the wiring comment in `nat_prelude.rs`), so inside this
/// crate only `to_comm_ring` and `field` have a non-test consumer today --
/// `rat_prelude` and `creal` re-derive the rest from the interned `AlgS`
/// root, which dead-code analysis cannot see.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub struct FieldNames {
    pub field: RecordNames,
    pub to_comm_ring: NameId,
    pub of_comm_ring: NameId,
    pub is_tight: NameId,
    pub apart_irrefl: NameId,
    pub apart_left_congr: NameId,
    pub apart_right_congr: NameId,
    pub inv_unique: NameId,
    pub mul_left_cancel: NameId,
    pub mul_neg_right: NameId,
}

/// What this module needs from `structures_setoid`'s extras.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldDeps {
    pub comm_ring_to_ring_s: NameId,
    pub mul_neg_one: NameId,
}

#[cfg(test)]
impl FieldNames {
    /// The three definitions plus the five theorems, for a test that wants to
    /// walk them.
    #[must_use]
    pub fn all(&self) -> [NameId; 9] {
        [
            self.mul_neg_right,
            self.to_comm_ring,
            self.of_comm_ring,
            self.is_tight,
            self.apart_irrefl,
            self.apart_left_congr,
            self.apart_right_congr,
            self.inv_unique,
            self.mul_left_cancel,
        ]
    }
}

/// Declare `AlgS.Field` and everything above. `cr` is this spine's own
/// `AlgS.CommRing` record; `algs` is the `AlgS` root name.
pub(crate) fn declare_field_setoid(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cr: &RecordNames,
    deps: FieldDeps,
    algs: NameId,
) -> Result<FieldNames, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);

    let field_name = k.name_str(algs, "Field");
    let specs = field_fields_s();
    assert_eq!(
        specs.len(),
        ix::FIELD_COUNT,
        "AlgS.Field field count drifted from `ix::FIELD_COUNT`"
    );
    let field = declare_record(k, lg, l0, l1, l2, field_name, &specs)?;

    let to_comm_ring = declare_to_comm_ring(k, &field, cr, field_name)?;
    let of_comm_ring = declare_of_comm_ring(k, lg, &field, cr, l1, field_name)?;
    let is_tight = declare_is_tight(k, lg, &field, field_name)?;
    let apart_irrefl = declare_apart_irrefl(k, lg, &field, field_name)?;
    let apart_left_congr = declare_apart_left_congr(k, lg, &field, field_name)?;
    let apart_right_congr = declare_apart_right_congr(k, &field, apart_left_congr, field_name)?;
    let inv_unique = declare_inv_unique(k, &field, field_name)?;
    let mul_left_cancel = declare_mul_left_cancel(k, lg, &field, l1, field_name)?;
    let mul_neg_right = declare_mul_neg_right(k, cr, deps, algs)?;

    Ok(FieldNames {
        field,
        to_comm_ring,
        of_comm_ring,
        is_tight,
        apart_irrefl,
        apart_left_congr,
        apart_right_congr,
        inv_unique,
        mul_left_cancel,
        mul_neg_right,
    })
}

#[cfg(test)]
#[path = "field_setoid_tests.rs"]
mod field_setoid_tests;
