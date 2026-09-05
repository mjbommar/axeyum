//! `CatS.*` — categories, functors and natural transformations **enriched in
//! setoids**: every hom-family carries its own equivalence relation, and every
//! composition/identity/associativity law is stated up to that equivalence
//! rather than up to `Eq`. This is roadmap item W3-3 and it is the direct
//! continuation of ADR-1595's decision (morphism equality is an explicit
//! equivalence, not function equality — there is no `funext` and no
//! `Quot.sound` in this kernel).
//!
//! # Why a hom-family needs no new machinery
//!
//! `AlgS.*` (ADR-1588) carries `equiv`/`equivRefl`/`equivSymm`/`equivTrans`
//! plus one congruence field per operation. A category is the same discipline
//! one level up: `homEquiv` with `homRefl`/`homSymm`/`homTrans` plus
//! `compCongr`, the single congruence the single operation (`comp`) needs.
//! The `AlgS` spine's own `FieldSpec`/`declare_record` machinery
//! ([`super::structures`]) builds it unchanged.
//!
//! # The universe story, measured
//!
//! [`super::structures::declare_record`] fixes **one universe level per
//! [`FieldKind`]** — `CarrierSort` selectors eliminate at `l2`, `Data` at
//! `l1`, `Law` at `l0` — which ADR-1609 recorded as "no record can hold
//! another record". That is a statement about *which level a field's type
//! sits at*, not about records, and both halves of it are measured here:
//!
//! | record | `obj` field | `hom` field | record lives at |
//! |---|---|---|---|
//! | [`CatS.Category`] | `Sort 1`, at level 2 → `CarrierSort` | `obj -> obj -> Sort 1`, at level **2** → `CarrierSort` | `Sort 2` |
//! | [`CatS.CategoryLarge`] | `Sort 2`, at level 3 → `CarrierSort` | `obj -> obj -> Sort 1`, at level **2** → `Data` | `Sort 3` |
//! | [`CatS.Functor`] | `src`/`tgt : CatS.Category`, at level 2 → `CarrierSort` | — | `Sort 2` |
//!
//! Three findings fall out:
//!
//! 1. **The same twelve-field list builds both categories**, at two level
//!    assignments, with exactly one `FieldKind` flipped (`hom`). Nothing had
//!    to be added to `declare_record`.
//! 2. **A record CAN hold a record here.** `CatS.Functor` has two fields of
//!    type `CatS.Category`, and `CatS.Category : Sort 2` is exactly `Sort l2`,
//!    so tagging them `CarrierSort` gives the selector the right elimination
//!    level. ADR-1609's blanket phrasing is too strong: what is fixed is the
//!    level *per kind*, and a record-typed field lands on the kind that
//!    already eliminates at `l2`.
//! 3. **Objects of the category of groups are expressible**
//!    ([`CatS.grpIndiscrete`] has `obj := AlgS.Group`), so the universe layer
//!    is not what blocks that category. See below for what does.
//!
//! # What blocks the category of `AlgS.Group`s, precisely
//!
//! Not universes — [`CatS.CategoryLarge`] takes `AlgS.Group` as its `obj`.
//! The obstruction is the **hom-family**: a morphism of groups is a function
//! *together with* a proof it respects `equiv` and a proof it preserves `op`,
//! and this kernel has no `Sigma` and no `Subtype` (both verified ABSENT,
//! ADR-1595), so that pair cannot be a type. Two escapes were checked and
//! both fail:
//!
//! - `hom G H := G.carrier -> H.carrier` (all functions) makes `compCongr`
//!   **false**: `g ∘ f ~ g' ∘ f'` needs `g'` to respect `G.equiv`, which an
//!   arbitrary function does not.
//! - `homEquiv f g := forall a b, G.equiv a b -> H.equiv (f a) (g b)` (the
//!   respectful relation, whose diagonal *is* "f is congruent") is a partial
//!   equivalence: `homRefl` is exactly the property being encoded and so
//!   cannot be a field.
//!
//! So the honest content of "the category of groups" is landed unbundled, in
//! the style ADR-1609 used for modules: [`CatS.IsGrpHom`] is the morphism
//! predicate and [`CatS.isGrpHom_id`] / [`CatS.isGrpHom_comp`] are the
//! category's identity and composition laws. Everything except the bundling
//! is here; the bundling is one `Sigma` away.
//!
//! # The setoid cost, measured
//!
//! [`CatS.ofMonoid`] — a monoid `M` deloops to a category whose hom-family is
//! `M.carrier` — is filled **entirely by `M`'s own fields**, with dummy object
//! binders in front and not one new proof obligation:
//!
//! | category field | supplied by |
//! |---|---|
//! | `homEquiv`/`homRefl`/`homSymm`/`homTrans` | `M.equiv`/`equivRefl`/`equivSymm`/`equivTrans` |
//! | `compCongr` | `M.opCongr` |
//! | `idL`/`idR`/`assoc` | `M.identL`/`identR`/`assoc` |
//!
//! That is the whole setoid tax at this layer: **zero**. The four
//! equivalence-infrastructure fields and the one congruence field a
//! setoid-enriched category carries are precisely the ones `AlgS` already
//! carries, so the first instance costs nothing to fill. Under `Eq` the same
//! five fields would be free but the instance would not exist at all — a
//! monoid whose equality is a defined relation (`CReal`) has no `Eq`-flavored
//! delooping.
//!
//! # Universal properties in this vocabulary
//!
//! [`CatS.IsInitial`] states initiality the way
//! `docs/research/08-planning/universal-property-template.md` part 2 requires
//! — the mediating map is a **given** `med : forall b, C.hom a b`, computed
//! and not extracted from an `Exists` — and [`CatS.initial_unique`] is the
//! theorem the template's two instances each prove by hand for their own
//! carrier: two initial objects are isomorphic, both composites equivalent to
//! the identity.
//!
//! `Nat.Peano.initial` and `Int.Characterization.initial` are **not**
//! recovered as instances, and the reason is the same missing `Sigma`: an
//! object of "pointed unary algebras" is a triple `(N, z, s)`, an object of
//! `ℤ`-structures a quadruple `(R, e, up, down)`, and `CatS.Category.obj` is a
//! single `Sort`. See ADR-1620.

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

use super::structures::{
    FieldKind, FieldSpec, RecordNames, app2, arrow, declare_record, lam_over, mk_instance, pi_over,
    sel,
};
use super::structures_setoid::idx as algs;

pub mod groups;

pub(crate) use groups::GroupCatDeps;
pub use groups::{GroupCatNames, GroupCatRecords};

// ---------------------------------------------------------------------------
// Free-variable block, disjoint from 21_xxx..24_xxx (poly/module/subgroup) and
// from `declare_record`'s own 10_000 / 10_900 range.
// ---------------------------------------------------------------------------

const C_FV: u64 = 25_000;
const D_FV: u64 = 25_001;
const E_FV: u64 = 25_002;

const OA_FV: u64 = 25_010;
const OB_FV: u64 = 25_011;
const OC_FV: u64 = 25_012;
const OD_FV: u64 = 25_013;

const MF_FV: u64 = 25_020;
const MG_FV: u64 = 25_021;
const MH_FV: u64 = 25_022;
const MF2_FV: u64 = 25_023;
const MG2_FV: u64 = 25_024;

const HY1_FV: u64 = 25_030;
const HY2_FV: u64 = 25_031;

const FO_FV: u64 = 25_040;
const FM_FV: u64 = 25_041;
const GO_FV: u64 = 25_042;
const GM_FV: u64 = 25_043;
const ETA_FV: u64 = 25_044;

const TA_FV: u64 = 25_050;
const TX_FV: u64 = 25_051;
const TXE_FV: u64 = 25_052;

const MON_M_FV: u64 = 25_060;
const MON_N_FV: u64 = 25_061;

const FN_FV: u64 = 25_070;
const FCONGR_FV: u64 = 25_071;
const FOP_FV: u64 = 25_072;
const FE_FV: u64 = 25_073;
const FN2_FV: u64 = 25_074;

const GRP_G_FV: u64 = 25_080;
const GRP_H_FV: u64 = 25_081;
const GRP_K_FV: u64 = 25_082;

const EL_A_FV: u64 = 25_090;
const EL_B_FV: u64 = 25_091;
const EL_N_FV: u64 = 25_092;

const MED_A_FV: u64 = 25_100;
const MED_B_FV: u64 = 25_101;
const HIA_FV: u64 = 25_110;
const HIB_FV: u64 = 25_111;

const FUNC_FV: u64 = 25_130;

/// Field indices, shared by [`CatS.Category`] and [`CatS.CategoryLarge`] —
/// the two records are the SAME field list at two universe assignments.
pub mod idx {
    pub const OBJ: usize = 0;
    pub const HOM: usize = 1;
    pub const HOM_EQUIV: usize = 2;
    pub const HOM_REFL: usize = 3;
    pub const HOM_SYMM: usize = 4;
    pub const HOM_TRANS: usize = 5;
    pub const ID: usize = 6;
    pub const COMP: usize = 7;
    #[allow(dead_code)]
    pub const COMP_CONGR: usize = 8;
    pub const ID_L: usize = 9;
    pub const ID_R: usize = 10;
    #[allow(dead_code)]
    pub const ASSOC: usize = 11;

    /// [`CatS.Functor`]'s own field indices.
    pub mod functor {
        pub const SRC: usize = 0;
        pub const TGT: usize = 1;
        pub const OBJ: usize = 2;
        pub const MAP: usize = 3;
        pub const MAP_CONGR: usize = 4;
        pub const MAP_ID: usize = 5;
        pub const MAP_COMP: usize = 6;
    }
}

use idx::{COMP, HOM, HOM_EQUIV, HOM_REFL, HOM_SYMM, HOM_TRANS, ID, ID_L, ID_R, OBJ};

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

// ---------------------------------------------------------------------------
// A category's eight pieces of data/infrastructure, however they were
// obtained: as `declare_record` `vals` while the record is being built, or as
// selector applications against a category VALUE.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct Cat {
    obj: ExprId,
    hom: ExprId,
    heq: ExprId,
    refl: ExprId,
    symm: ExprId,
    trans: ExprId,
    id: ExprId,
    comp: ExprId,
}

/// The selectors of `rn` applied to the category value `c`.
fn cat_of(k: &mut Kernel, rn: &RecordNames, c: ExprId) -> Cat {
    Cat {
        obj: sel(k, rn, OBJ, c),
        hom: sel(k, rn, HOM, c),
        heq: sel(k, rn, HOM_EQUIV, c),
        refl: sel(k, rn, HOM_REFL, c),
        symm: sel(k, rn, HOM_SYMM, c),
        trans: sel(k, rn, HOM_TRANS, c),
        id: sel(k, rn, ID, c),
        comp: sel(k, rn, COMP, c),
    }
}

impl Cat {
    fn hom_ty(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.hom, a, b)
    }
    fn eqv(&self, k: &mut Kernel, a: ExprId, b: ExprId, f: ExprId, g: ExprId) -> ExprId {
        t_app(k, self.heq, &[a, b, f, g])
    }
    fn ident(&self, k: &mut Kernel, a: ExprId) -> ExprId {
        k.app(self.id, a)
    }
    fn cmp(&self, k: &mut Kernel, a: ExprId, b: ExprId, c: ExprId, g: ExprId, f: ExprId) -> ExprId {
        t_app(k, self.comp, &[a, b, c, g, f])
    }
    fn rfl(&self, k: &mut Kernel, a: ExprId, b: ExprId, f: ExprId) -> ExprId {
        t_app(k, self.refl, &[a, b, f])
    }
    fn sy(&self, k: &mut Kernel, a: ExprId, b: ExprId, f: ExprId, g: ExprId, h: ExprId) -> ExprId {
        t_app(k, self.symm, &[a, b, f, g, h])
    }
    #[allow(clippy::too_many_arguments)]
    fn tr(
        &self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        f: ExprId,
        g: ExprId,
        h: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        t_app(k, self.trans, &[a, b, f, g, h, h1, h2])
    }
}

// ---------------------------------------------------------------------------
// The twelve field shapes. Every LAW field applies the record's own
// `homEquiv` VALUE, exactly as `AlgS`'s law fields apply its `equiv`.
// ---------------------------------------------------------------------------

/// `Sort l1` — the objects. `l1` is 1 for [`CatS.Category`], 2 for
/// [`CatS.CategoryLarge`].
fn obj_field() -> FieldSpec {
    FieldSpec {
        suffix: "obj",
        kind: FieldKind::CarrierSort,
        build: Box::new(|k, _lg, l1, _vals| k.sort(l1)),
    }
}

/// `obj -> obj -> Sort 1` — the hom-family. Always lands in `Sort 1`; only
/// the OBJECT level moves between the two records, which is why this field's
/// [`FieldKind`] flips (level 2 is `l2` when objects are small and `l1` when
/// they are large).
fn hom_field(kind: FieldKind) -> FieldSpec {
    FieldSpec {
        suffix: "hom",
        kind,
        build: Box::new(|k, _lg, _l1, vals| {
            let o = vals[OBJ];
            let l0 = k.level_zero();
            let one = k.level_succ(l0);
            let s = k.sort(one);
            let inner = arrow(k, o, s);
            arrow(k, o, inner)
        }),
    }
}

/// `forall (a b : obj), hom a b -> hom a b -> Prop`.
fn hom_equiv_field() -> FieldSpec {
    FieldSpec {
        suffix: "homEquiv",
        kind: FieldKind::Data,
        build: Box::new(|k, _lg, _l1, vals| {
            let o = vals[OBJ];
            let hom = vals[HOM];
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let h = app2(k, hom, a, b);
            let l0 = k.level_zero();
            let prop = k.sort(l0);
            let inner = arrow(k, h, prop);
            let inner = arrow(k, h, inner);
            let t = pi_over(k, OB_FV, o, inner);
            pi_over(k, OA_FV, o, t)
        }),
    }
}

/// `forall (a b : obj) (f : hom a b), homEquiv a b f f`.
fn hom_refl_field() -> FieldSpec {
    FieldSpec {
        suffix: "homRefl",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let o = vals[OBJ];
            let hom = vals[HOM];
            let heq = vals[HOM_EQUIV];
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let h = app2(k, hom, a, b);
            let f = k.fvar(MF_FV);
            let body = t_app(k, heq, &[a, b, f, f]);
            let t = pi_over(k, MF_FV, h, body);
            let t = pi_over(k, OB_FV, o, t);
            pi_over(k, OA_FV, o, t)
        }),
    }
}

/// `forall (a b : obj) (f g : hom a b), homEquiv a b f g -> homEquiv a b g f`.
fn hom_symm_field() -> FieldSpec {
    FieldSpec {
        suffix: "homSymm",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let o = vals[OBJ];
            let hom = vals[HOM];
            let heq = vals[HOM_EQUIV];
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let h = app2(k, hom, a, b);
            let f = k.fvar(MF_FV);
            let g = k.fvar(MG_FV);
            let hyp = t_app(k, heq, &[a, b, f, g]);
            let concl = t_app(k, heq, &[a, b, g, f]);
            let t = arrow(k, hyp, concl);
            let t = pi_over(k, MG_FV, h, t);
            let t = pi_over(k, MF_FV, h, t);
            let t = pi_over(k, OB_FV, o, t);
            pi_over(k, OA_FV, o, t)
        }),
    }
}

/// `forall (a b : obj) (f g h : hom a b), homEquiv a b f g -> homEquiv a b g h
/// -> homEquiv a b f h`.
fn hom_trans_field() -> FieldSpec {
    FieldSpec {
        suffix: "homTrans",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let o = vals[OBJ];
            let hom = vals[HOM];
            let heq = vals[HOM_EQUIV];
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let hty = app2(k, hom, a, b);
            let f = k.fvar(MF_FV);
            let g = k.fvar(MG_FV);
            let h = k.fvar(MH_FV);
            let hyp1 = t_app(k, heq, &[a, b, f, g]);
            let hyp2 = t_app(k, heq, &[a, b, g, h]);
            let concl = t_app(k, heq, &[a, b, f, h]);
            let t = arrow(k, hyp2, concl);
            let t = arrow(k, hyp1, t);
            let t = pi_over(k, MH_FV, hty, t);
            let t = pi_over(k, MG_FV, hty, t);
            let t = pi_over(k, MF_FV, hty, t);
            let t = pi_over(k, OB_FV, o, t);
            pi_over(k, OA_FV, o, t)
        }),
    }
}

/// `forall (a : obj), hom a a`.
fn id_field() -> FieldSpec {
    FieldSpec {
        suffix: "id",
        kind: FieldKind::Data,
        build: Box::new(|k, _lg, _l1, vals| {
            let o = vals[OBJ];
            let hom = vals[HOM];
            let a = k.fvar(OA_FV);
            let body = app2(k, hom, a, a);
            pi_over(k, OA_FV, o, body)
        }),
    }
}

/// `forall (a b c : obj), hom b c -> hom a b -> hom a c`.
fn comp_field() -> FieldSpec {
    FieldSpec {
        suffix: "comp",
        kind: FieldKind::Data,
        build: Box::new(|k, _lg, _l1, vals| {
            let o = vals[OBJ];
            let hom = vals[HOM];
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let c = k.fvar(OC_FV);
            let hbc = app2(k, hom, b, c);
            let hab = app2(k, hom, a, b);
            let hac = app2(k, hom, a, c);
            let t = arrow(k, hab, hac);
            let t = arrow(k, hbc, t);
            let t = pi_over(k, OC_FV, o, t);
            let t = pi_over(k, OB_FV, o, t);
            pi_over(k, OA_FV, o, t)
        }),
    }
}

/// `forall (a b c : obj) (g g' : hom b c) (f f' : hom a b),
///  homEquiv b c g g' -> homEquiv a b f f' ->
///  homEquiv a c (comp a b c g f) (comp a b c g' f')` — **the single
/// congruence a setoid-enriched category owes**, the exact analogue of
/// `AlgS.Magma.opCongr`.
fn comp_congr_field() -> FieldSpec {
    FieldSpec {
        suffix: "compCongr",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let c = cat_from_vals(vals);
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let cc = k.fvar(OC_FV);
            let hbc = c.hom_ty(k, b, cc);
            let hab = c.hom_ty(k, a, b);
            let g = k.fvar(MG_FV);
            let g2 = k.fvar(MG2_FV);
            let f = k.fvar(MF_FV);
            let f2 = k.fvar(MF2_FV);
            let hyp1 = c.eqv(k, b, cc, g, g2);
            let hyp2 = c.eqv(k, a, b, f, f2);
            let lhs = c.cmp(k, a, b, cc, g, f);
            let rhs = c.cmp(k, a, b, cc, g2, f2);
            let concl = c.eqv(k, a, cc, lhs, rhs);
            let t = arrow(k, hyp2, concl);
            let t = arrow(k, hyp1, t);
            let t = pi_over(k, MF2_FV, hab, t);
            let t = pi_over(k, MF_FV, hab, t);
            let t = pi_over(k, MG2_FV, hbc, t);
            let t = pi_over(k, MG_FV, hbc, t);
            let t = pi_over(k, OC_FV, c.obj, t);
            let t = pi_over(k, OB_FV, c.obj, t);
            pi_over(k, OA_FV, c.obj, t)
        }),
    }
}

/// `forall (a b : obj) (f : hom a b), homEquiv a b (comp a b b (id b) f) f`.
fn id_l_field() -> FieldSpec {
    FieldSpec {
        suffix: "idL",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let c = cat_from_vals(vals);
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let hab = c.hom_ty(k, a, b);
            let f = k.fvar(MF_FV);
            let ib = c.ident(k, b);
            let lhs = c.cmp(k, a, b, b, ib, f);
            let body = c.eqv(k, a, b, lhs, f);
            let t = pi_over(k, MF_FV, hab, body);
            let t = pi_over(k, OB_FV, c.obj, t);
            pi_over(k, OA_FV, c.obj, t)
        }),
    }
}

/// `forall (a b : obj) (f : hom a b), homEquiv a b (comp a a b f (id a)) f`.
fn id_r_field() -> FieldSpec {
    FieldSpec {
        suffix: "idR",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let c = cat_from_vals(vals);
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let hab = c.hom_ty(k, a, b);
            let f = k.fvar(MF_FV);
            let ia = c.ident(k, a);
            let lhs = c.cmp(k, a, a, b, f, ia);
            let body = c.eqv(k, a, b, lhs, f);
            let t = pi_over(k, MF_FV, hab, body);
            let t = pi_over(k, OB_FV, c.obj, t);
            pi_over(k, OA_FV, c.obj, t)
        }),
    }
}

/// `forall (a b c d : obj) (h : hom c d) (g : hom b c) (f : hom a b),
///  homEquiv a d (comp a b d (comp b c d h g) f) (comp a c d h (comp a b c g f))`
/// — `(h ∘ g) ∘ f ~ h ∘ (g ∘ f)`, the orientation `AlgS.Monoid.assoc` already
/// has, so [`CatS.ofMonoid`] can supply it verbatim.
fn assoc_field() -> FieldSpec {
    FieldSpec {
        suffix: "assoc",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let c = cat_from_vals(vals);
            let a = k.fvar(OA_FV);
            let b = k.fvar(OB_FV);
            let cc = k.fvar(OC_FV);
            let d = k.fvar(OD_FV);
            let hcd = c.hom_ty(k, cc, d);
            let hbc = c.hom_ty(k, b, cc);
            let hab = c.hom_ty(k, a, b);
            let h = k.fvar(MH_FV);
            let g = k.fvar(MG_FV);
            let f = k.fvar(MF_FV);
            let hg = c.cmp(k, b, cc, d, h, g);
            let lhs = c.cmp(k, a, b, d, hg, f);
            let gf = c.cmp(k, a, b, cc, g, f);
            let rhs = c.cmp(k, a, cc, d, h, gf);
            let body = c.eqv(k, a, d, lhs, rhs);
            let t = pi_over(k, MF_FV, hab, body);
            let t = pi_over(k, MG_FV, hbc, t);
            let t = pi_over(k, MH_FV, hcd, t);
            let t = pi_over(k, OD_FV, c.obj, t);
            let t = pi_over(k, OC_FV, c.obj, t);
            let t = pi_over(k, OB_FV, c.obj, t);
            pi_over(k, OA_FV, c.obj, t)
        }),
    }
}

/// The `vals` slice as a [`Cat`]. Only sound once `comp` (index 7) has been
/// built, which is true for every field that calls it.
fn cat_from_vals(vals: &[ExprId]) -> Cat {
    Cat {
        obj: vals[OBJ],
        hom: vals[HOM],
        heq: vals[HOM_EQUIV],
        refl: vals[HOM_REFL],
        symm: vals[HOM_SYMM],
        trans: vals[HOM_TRANS],
        id: vals[ID],
        comp: vals[COMP],
    }
}

/// The twelve fields, in order. `hom_kind` is the ONLY thing that differs
/// between the small and the large category.
fn category_fields(hom_kind: FieldKind) -> Vec<FieldSpec> {
    vec![
        obj_field(),
        hom_field(hom_kind),
        hom_equiv_field(),
        hom_refl_field(),
        hom_symm_field(),
        hom_trans_field(),
        id_field(),
        comp_field(),
        comp_congr_field(),
        id_l_field(),
        id_r_field(),
        assoc_field(),
    ]
}

// ---------------------------------------------------------------------------
// `CatS.Functor` — the record that holds two records.
// ---------------------------------------------------------------------------

/// `forall (a b : src.obj) (f g : src.hom a b), src.homEquiv a b f g ->
///  tgt.homEquiv (Fo a) (Fo b) (Fm a b f) (Fm a b g)`.
fn functor_congr_stmt(k: &mut Kernel, c: &Cat, d: &Cat, fo: ExprId, fm: ExprId) -> ExprId {
    let a = k.fvar(OA_FV);
    let b = k.fvar(OB_FV);
    let hab = c.hom_ty(k, a, b);
    let f = k.fvar(MF_FV);
    let g = k.fvar(MG_FV);
    let hyp = c.eqv(k, a, b, f, g);
    let foa = k.app(fo, a);
    let fob = k.app(fo, b);
    let fmf = t_app(k, fm, &[a, b, f]);
    let fmg = t_app(k, fm, &[a, b, g]);
    let concl = d.eqv(k, foa, fob, fmf, fmg);
    let t = arrow(k, hyp, concl);
    let t = pi_over(k, MG_FV, hab, t);
    let t = pi_over(k, MF_FV, hab, t);
    let t = pi_over(k, OB_FV, c.obj, t);
    pi_over(k, OA_FV, c.obj, t)
}

/// `forall (a : src.obj), tgt.homEquiv (Fo a) (Fo a) (Fm a a (src.id a))
///  (tgt.id (Fo a))`.
fn functor_id_stmt(k: &mut Kernel, c: &Cat, d: &Cat, fo: ExprId, fm: ExprId) -> ExprId {
    let a = k.fvar(OA_FV);
    let ia = c.ident(k, a);
    let lhs = t_app(k, fm, &[a, a, ia]);
    let foa = k.app(fo, a);
    let rhs = d.ident(k, foa);
    let body = d.eqv(k, foa, foa, lhs, rhs);
    pi_over(k, OA_FV, c.obj, body)
}

/// `forall (a b c : src.obj) (g : src.hom b c) (f : src.hom a b),
///  tgt.homEquiv (Fo a) (Fo c) (Fm a c (src.comp a b c g f))
///    (tgt.comp (Fo a) (Fo b) (Fo c) (Fm b c g) (Fm a b f))`.
fn functor_comp_stmt(k: &mut Kernel, c: &Cat, d: &Cat, fo: ExprId, fm: ExprId) -> ExprId {
    let a = k.fvar(OA_FV);
    let b = k.fvar(OB_FV);
    let cc = k.fvar(OC_FV);
    let hbc = c.hom_ty(k, b, cc);
    let hab = c.hom_ty(k, a, b);
    let g = k.fvar(MG_FV);
    let f = k.fvar(MF_FV);
    let gf = c.cmp(k, a, b, cc, g, f);
    let lhs = t_app(k, fm, &[a, cc, gf]);
    let foa = k.app(fo, a);
    let fob = k.app(fo, b);
    let foc = k.app(fo, cc);
    let fmg = t_app(k, fm, &[b, cc, g]);
    let fmf = t_app(k, fm, &[a, b, f]);
    let rhs = d.cmp(k, foa, fob, foc, fmg, fmf);
    let body = d.eqv(k, foa, foc, lhs, rhs);
    let t = pi_over(k, MF_FV, hab, body);
    let t = pi_over(k, MG_FV, hbc, t);
    let t = pi_over(k, OC_FV, c.obj, t);
    let t = pi_over(k, OB_FV, c.obj, t);
    pi_over(k, OA_FV, c.obj, t)
}

/// `Fo`'s type: `src.obj -> tgt.obj`.
fn fo_ty(k: &mut Kernel, c: &Cat, d: &Cat) -> ExprId {
    arrow(k, c.obj, d.obj)
}

/// `Fm`'s type: `forall (a b : src.obj), src.hom a b -> tgt.hom (Fo a) (Fo b)`.
fn fm_ty(k: &mut Kernel, c: &Cat, d: &Cat, fo: ExprId) -> ExprId {
    let a = k.fvar(OA_FV);
    let b = k.fvar(OB_FV);
    let hab = c.hom_ty(k, a, b);
    let foa = k.app(fo, a);
    let fob = k.app(fo, b);
    let tgt = d.hom_ty(k, foa, fob);
    let t = arrow(k, hab, tgt);
    let t = pi_over(k, OB_FV, c.obj, t);
    pi_over(k, OA_FV, c.obj, t)
}

fn functor_fields(cat: RecordNames) -> Vec<FieldSpec> {
    use idx::functor::{OBJ as F_OBJ, SRC, TGT};
    let (cat_src, cat_tgt) = (cat, cat);
    let (cat_o, cat_m, cat_c, cat_i, cat_p) = (cat, cat, cat, cat, cat);
    vec![
        FieldSpec {
            suffix: "src",
            kind: FieldKind::CarrierSort,
            build: Box::new(move |k, _lg, _l1, _vals| k.const_(cat_src.ind, vec![])),
        },
        FieldSpec {
            suffix: "tgt",
            kind: FieldKind::CarrierSort,
            build: Box::new(move |k, _lg, _l1, _vals| k.const_(cat_tgt.ind, vec![])),
        },
        FieldSpec {
            suffix: "obj",
            kind: FieldKind::Data,
            build: Box::new(move |k, _lg, _l1, vals| {
                let c = cat_of(k, &cat_o, vals[SRC]);
                let d = cat_of(k, &cat_o, vals[TGT]);
                fo_ty(k, &c, &d)
            }),
        },
        FieldSpec {
            suffix: "map",
            kind: FieldKind::Data,
            build: Box::new(move |k, _lg, _l1, vals| {
                let c = cat_of(k, &cat_m, vals[SRC]);
                let d = cat_of(k, &cat_m, vals[TGT]);
                fm_ty(k, &c, &d, vals[F_OBJ])
            }),
        },
        FieldSpec {
            suffix: "mapCongr",
            kind: FieldKind::Law,
            build: Box::new(move |k, _lg, _l1, vals| {
                let c = cat_of(k, &cat_c, vals[SRC]);
                let d = cat_of(k, &cat_c, vals[TGT]);
                functor_congr_stmt(k, &c, &d, vals[F_OBJ], vals[idx::functor::MAP])
            }),
        },
        FieldSpec {
            suffix: "mapId",
            kind: FieldKind::Law,
            build: Box::new(move |k, _lg, _l1, vals| {
                let c = cat_of(k, &cat_i, vals[SRC]);
                let d = cat_of(k, &cat_i, vals[TGT]);
                functor_id_stmt(k, &c, &d, vals[F_OBJ], vals[idx::functor::MAP])
            }),
        },
        FieldSpec {
            suffix: "mapComp",
            kind: FieldKind::Law,
            build: Box::new(move |k, _lg, _l1, vals| {
                let c = cat_of(k, &cat_p, vals[SRC]);
                let d = cat_of(k, &cat_p, vals[TGT]);
                functor_comp_stmt(k, &c, &d, vals[F_OBJ], vals[idx::functor::MAP])
            }),
        },
    ]
}

// ---------------------------------------------------------------------------
// `And` plumbing over three conjuncts.
// ---------------------------------------------------------------------------

fn and3(k: &mut Kernel, lg: &LogicPrelude, p: &[ExprId; 3]) -> ExprId {
    let and_c = k.const_(lg.and, vec![]);
    let tail = app2(k, and_c, p[1], p[2]);
    let and_c2 = k.const_(lg.and, vec![]);
    app2(k, and_c2, p[0], tail)
}

fn intro3(k: &mut Kernel, lg: &LogicPrelude, p: &[ExprId; 3], v: &[ExprId; 3]) -> ExprId {
    let and_c = k.const_(lg.and, vec![]);
    let tail_prop = app2(k, and_c, p[1], p[2]);
    let ai = k.const_(lg.and_intro, vec![]);
    let tail = t_app(k, ai, &[p[1], p[2], v[1], v[2]]);
    let ai2 = k.const_(lg.and_intro, vec![]);
    t_app(k, ai2, &[p[0], tail_prop, v[0], tail])
}

/// Project conjunct `which` (0..2) out of a proof of [`and3`].
fn project3(k: &mut Kernel, lg: &LogicPrelude, p: &[ExprId; 3], h: ExprId, which: usize) -> ExprId {
    let and_c = k.const_(lg.and, vec![]);
    let tail_prop = app2(k, and_c, p[1], p[2]);
    match which {
        0 => {
            let al = k.const_(lg.and_left, vec![]);
            t_app(k, al, &[p[0], tail_prop, h])
        }
        1 => {
            let ar = k.const_(lg.and_right, vec![]);
            let rest = t_app(k, ar, &[p[0], tail_prop, h]);
            let al = k.const_(lg.and_left, vec![]);
            t_app(k, al, &[p[1], p[2], rest])
        }
        _ => {
            let ar = k.const_(lg.and_right, vec![]);
            let rest = t_app(k, ar, &[p[0], tail_prop, h]);
            let ar2 = k.const_(lg.and_right, vec![]);
            t_app(k, ar2, &[p[1], p[2], rest])
        }
    }
}

// ---------------------------------------------------------------------------
// Names.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CategoryRecords {
    pub category: RecordNames,
    pub category_large: RecordNames,
    pub functor: RecordNames,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CategoryNames {
    pub indiscrete: NameId,
    pub of_monoid: NameId,
    pub large_indiscrete: NameId,
    pub grp_indiscrete: NameId,
    pub id_functor: NameId,
    pub of_monoid_hom: NameId,
    pub is_functor: NameId,
    pub is_nat: NameId,
    pub is_initial: NameId,
    pub is_terminal: NameId,
    pub is_grp_hom: NameId,
    pub functor_is_functor: NameId,
    pub is_functor_id: NameId,
    pub is_functor_comp: NameId,
    pub is_nat_id: NameId,
    pub is_nat_of_monoid: NameId,
    pub initial_unique: NameId,
    pub indiscrete_is_initial: NameId,
    pub indiscrete_is_terminal: NameId,
    pub is_grp_hom_id: NameId,
    pub is_grp_hom_comp: NameId,
}

#[cfg(test)]
impl CategoryNames {
    #[must_use]
    pub fn all(&self) -> [NameId; 21] {
        [
            self.indiscrete,
            self.of_monoid,
            self.large_indiscrete,
            self.grp_indiscrete,
            self.id_functor,
            self.of_monoid_hom,
            self.is_functor,
            self.is_nat,
            self.is_initial,
            self.is_terminal,
            self.is_grp_hom,
            self.functor_is_functor,
            self.is_functor_id,
            self.is_functor_comp,
            self.is_nat_id,
            self.is_nat_of_monoid,
            self.initial_unique,
            self.indiscrete_is_initial,
            self.indiscrete_is_terminal,
            self.is_grp_hom_id,
            self.is_grp_hom_comp,
        ]
    }

    #[must_use]
    pub fn theorems(&self) -> [NameId; 9] {
        [
            self.functor_is_functor,
            self.is_functor_id,
            self.is_functor_comp,
            self.is_nat_id,
            self.is_nat_of_monoid,
            self.initial_unique,
            self.indiscrete_is_initial,
            self.indiscrete_is_terminal,
            self.is_grp_hom_id,
        ]
    }
}

// ---------------------------------------------------------------------------
// The records.
// ---------------------------------------------------------------------------

/// Declare `CatS.Category`, `CatS.CategoryLarge` and `CatS.Functor`.
pub(crate) fn declare_category_records(
    k: &mut Kernel,
    lg: &LogicPrelude,
    ns: NameId,
) -> Result<CategoryRecords, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);
    let l3 = k.level_succ(l2);

    let cat_name = k.name_str(ns, "Category");
    let category = declare_record(
        k,
        lg,
        l0,
        l1,
        l2,
        cat_name,
        &category_fields(FieldKind::CarrierSort),
    )?;

    // The SAME field list one universe up: objects at `Sort 2`, hom-sets still
    // at `Sort 1`, so the `hom` field's type drops from `l2` to `l1` and its
    // kind flips with it.
    let large_name = k.name_str(ns, "CategoryLarge");
    let category_large = declare_record(
        k,
        lg,
        l0,
        l2,
        l3,
        large_name,
        &category_fields(FieldKind::Data),
    )?;

    let functor_name = k.name_str(ns, "Functor");
    let functor = declare_record(k, lg, l0, l1, l2, functor_name, &functor_fields(category))?;

    Ok(CategoryRecords {
        category,
        category_large,
        functor,
    })
}

// ---------------------------------------------------------------------------
// Instances of `CatS.Category`.
// ---------------------------------------------------------------------------

/// `CatS.indiscrete : forall (A : Sort 1), CatS.Category` — objects `A`,
/// hom-sets `A`, and **every parallel pair identified** by `homEquiv := True`.
/// One morphism between any two objects, said without a quotient: this is
/// exactly the setoid enrichment doing the work `Quot.sound` would otherwise
/// be asked for (ADR-1595).
fn declare_indiscrete(
    k: &mut Kernel,
    lg: &LogicPrelude,
    rec: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sort1 = k.sort(l1);
    let a_ty = k.fvar(TA_FV);
    let true_c = k.const_(lg.true_, vec![]);
    let ti = k.const_(lg.true_intro, vec![]);

    // hom := fun _ _ => A
    let hom = {
        let inner = lam_over(k, OB_FV, a_ty, a_ty);
        lam_over(k, OA_FV, a_ty, inner)
    };
    // homEquiv := fun _ _ _ _ => True
    let heq = {
        let t = lam_over(k, MG_FV, a_ty, true_c);
        let t = lam_over(k, MF_FV, a_ty, t);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };
    let triv = |k: &mut Kernel, binders: &[(u64, ExprId)]| -> ExprId {
        let mut e = ti;
        for (fv, ty) in binders.iter().rev() {
            e = lam_over(k, *fv, *ty, e);
        }
        e
    };
    let refl = triv(k, &[(OA_FV, a_ty), (OB_FV, a_ty), (MF_FV, a_ty)]);
    let symm = triv(
        k,
        &[
            (OA_FV, a_ty),
            (OB_FV, a_ty),
            (MF_FV, a_ty),
            (MG_FV, a_ty),
            (HY1_FV, true_c),
        ],
    );
    let trans = triv(
        k,
        &[
            (OA_FV, a_ty),
            (OB_FV, a_ty),
            (MF_FV, a_ty),
            (MG_FV, a_ty),
            (MH_FV, a_ty),
            (HY1_FV, true_c),
            (HY2_FV, true_c),
        ],
    );
    // id := fun a => a
    let id = {
        let a = k.fvar(OA_FV);
        lam_over(k, OA_FV, a_ty, a)
    };
    // comp := fun a b c g f => g
    let comp = {
        let g = k.fvar(MG_FV);
        let t = lam_over(k, MF_FV, a_ty, g);
        let t = lam_over(k, MG_FV, a_ty, t);
        let t = lam_over(k, OC_FV, a_ty, t);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };
    let comp_congr = triv(
        k,
        &[
            (OA_FV, a_ty),
            (OB_FV, a_ty),
            (OC_FV, a_ty),
            (MG_FV, a_ty),
            (MG2_FV, a_ty),
            (MF_FV, a_ty),
            (MF2_FV, a_ty),
            (HY1_FV, true_c),
            (HY2_FV, true_c),
        ],
    );
    let id_l = triv(k, &[(OA_FV, a_ty), (OB_FV, a_ty), (MF_FV, a_ty)]);
    let id_r = triv(k, &[(OA_FV, a_ty), (OB_FV, a_ty), (MF_FV, a_ty)]);
    let assoc = triv(
        k,
        &[
            (OA_FV, a_ty),
            (OB_FV, a_ty),
            (OC_FV, a_ty),
            (OD_FV, a_ty),
            (MH_FV, a_ty),
            (MG_FV, a_ty),
            (MF_FV, a_ty),
        ],
    );

    let body = mk_instance(
        k,
        rec,
        &[
            a_ty, hom, heq, refl, symm, trans, id, comp, comp_congr, id_l, id_r, assoc,
        ],
    );
    let value = lam_over(k, TA_FV, sort1, body);
    let cat_ty = k.const_(rec.ind, vec![]);
    let ty = pi_over(k, TA_FV, sort1, cat_ty);

    let name = k.name_str(ns, "indiscrete");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `CatS.ofMonoid : forall (A : Sort 1) (M : AlgS.Monoid), CatS.Category` —
/// the delooping. **Every field is one of `M`'s own**, so this instance is the
/// measurement of the setoid cost: zero new obligations.
fn declare_of_monoid(
    k: &mut Kernel,
    rec: &RecordNames,
    monoid: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use algs::monoid::{
        ASSOC as M_ASSOC, CARRIER, E, EQUIV, EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, IDENT_L, IDENT_R,
        OP, OP_CONGR,
    };
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sort1 = k.sort(l1);
    let a_ty = k.fvar(TA_FV);
    let m = k.fvar(MON_M_FV);
    let mon_ty = k.const_(monoid.ind, vec![]);

    let carrier = sel(k, monoid, CARRIER, m);

    // Two dummy object binders in front of `M`'s field, three for `comp`.
    let under2 = |k: &mut Kernel, inner: ExprId| -> ExprId {
        let t = lam_over(k, OB_FV, a_ty, inner);
        lam_over(k, OA_FV, a_ty, t)
    };
    let under3 = |k: &mut Kernel, inner: ExprId| -> ExprId {
        let t = lam_over(k, OC_FV, a_ty, inner);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };
    let under4 = |k: &mut Kernel, inner: ExprId| -> ExprId {
        let t = lam_over(k, OD_FV, a_ty, inner);
        let t = lam_over(k, OC_FV, a_ty, t);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };

    let hom = under2(k, carrier);
    let m_equiv = sel(k, monoid, EQUIV, m);
    let heq = under2(k, m_equiv);
    let m_refl = sel(k, monoid, EQUIV_REFL, m);
    let refl = under2(k, m_refl);
    let m_symm = sel(k, monoid, EQUIV_SYMM, m);
    let symm = under2(k, m_symm);
    let m_trans = sel(k, monoid, EQUIV_TRANS, m);
    let trans = under2(k, m_trans);
    let m_e = sel(k, monoid, E, m);
    let id = lam_over(k, OA_FV, a_ty, m_e);
    let m_op = sel(k, monoid, OP, m);
    let comp = under3(k, m_op);
    let m_op_congr = sel(k, monoid, OP_CONGR, m);
    let comp_congr = under3(k, m_op_congr);
    let m_ident_l = sel(k, monoid, IDENT_L, m);
    let id_l = under2(k, m_ident_l);
    let m_ident_r = sel(k, monoid, IDENT_R, m);
    let id_r = under2(k, m_ident_r);
    let m_assoc = sel(k, monoid, M_ASSOC, m);
    let assoc = under4(k, m_assoc);

    let body = mk_instance(
        k,
        rec,
        &[
            a_ty, hom, heq, refl, symm, trans, id, comp, comp_congr, id_l, id_r, assoc,
        ],
    );
    let value = lam_over(k, MON_M_FV, mon_ty, body);
    let value = lam_over(k, TA_FV, sort1, value);
    let cat_ty = k.const_(rec.ind, vec![]);
    let ty = pi_over(k, MON_M_FV, mon_ty, cat_ty);
    let ty = pi_over(k, TA_FV, sort1, ty);

    let name = k.name_str(ns, "ofMonoid");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `CatS.largeIndiscrete : forall (A : Sort 2) (X : Sort 1) (x : X),
///  CatS.CategoryLarge` — the same construction one universe up, so that
/// **objects may be `AlgS` records**.
fn declare_large_indiscrete(
    k: &mut Kernel,
    lg: &LogicPrelude,
    rec: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);
    let sort1 = k.sort(l1);
    let sort2 = k.sort(l2);
    let a_ty = k.fvar(TA_FV);
    let x_ty = k.fvar(TX_FV);
    let x = k.fvar(TXE_FV);
    let true_c = k.const_(lg.true_, vec![]);
    let ti = k.const_(lg.true_intro, vec![]);

    let hom = {
        let inner = lam_over(k, OB_FV, a_ty, x_ty);
        lam_over(k, OA_FV, a_ty, inner)
    };
    let heq = {
        let t = lam_over(k, MG_FV, x_ty, true_c);
        let t = lam_over(k, MF_FV, x_ty, t);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };
    let triv = |k: &mut Kernel, binders: &[(u64, ExprId)]| -> ExprId {
        let mut e = ti;
        for (fv, ty) in binders.iter().rev() {
            e = lam_over(k, *fv, *ty, e);
        }
        e
    };
    let refl = triv(k, &[(OA_FV, a_ty), (OB_FV, a_ty), (MF_FV, x_ty)]);
    let symm = triv(
        k,
        &[
            (OA_FV, a_ty),
            (OB_FV, a_ty),
            (MF_FV, x_ty),
            (MG_FV, x_ty),
            (HY1_FV, true_c),
        ],
    );
    let trans = triv(
        k,
        &[
            (OA_FV, a_ty),
            (OB_FV, a_ty),
            (MF_FV, x_ty),
            (MG_FV, x_ty),
            (MH_FV, x_ty),
            (HY1_FV, true_c),
            (HY2_FV, true_c),
        ],
    );
    let id = lam_over(k, OA_FV, a_ty, x);
    let comp = {
        let g = k.fvar(MG_FV);
        let t = lam_over(k, MF_FV, x_ty, g);
        let t = lam_over(k, MG_FV, x_ty, t);
        let t = lam_over(k, OC_FV, a_ty, t);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };
    let comp_congr = triv(
        k,
        &[
            (OA_FV, a_ty),
            (OB_FV, a_ty),
            (OC_FV, a_ty),
            (MG_FV, x_ty),
            (MG2_FV, x_ty),
            (MF_FV, x_ty),
            (MF2_FV, x_ty),
            (HY1_FV, true_c),
            (HY2_FV, true_c),
        ],
    );
    let id_l = triv(k, &[(OA_FV, a_ty), (OB_FV, a_ty), (MF_FV, x_ty)]);
    let id_r = triv(k, &[(OA_FV, a_ty), (OB_FV, a_ty), (MF_FV, x_ty)]);
    let assoc = triv(
        k,
        &[
            (OA_FV, a_ty),
            (OB_FV, a_ty),
            (OC_FV, a_ty),
            (OD_FV, a_ty),
            (MH_FV, x_ty),
            (MG_FV, x_ty),
            (MF_FV, x_ty),
        ],
    );

    let body = mk_instance(
        k,
        rec,
        &[
            a_ty, hom, heq, refl, symm, trans, id, comp, comp_congr, id_l, id_r, assoc,
        ],
    );
    let value = lam_over(k, TXE_FV, x_ty, body);
    let value = lam_over(k, TX_FV, sort1, value);
    let value = lam_over(k, TA_FV, sort2, value);

    let cat_ty = k.const_(rec.ind, vec![]);
    let ty = pi_over(k, TXE_FV, x_ty, cat_ty);
    let ty = pi_over(k, TX_FV, sort1, ty);
    let ty = pi_over(k, TA_FV, sort2, ty);

    let name = k.name_str(ns, "largeIndiscrete");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `CatS.grpIndiscrete : CatS.CategoryLarge` — **objects are `AlgS.Group`**.
/// The measurement: nothing about universes stops the category of groups; it
/// is the hom-family that needs a `Sigma` this kernel does not have.
fn declare_grp_indiscrete(
    k: &mut Kernel,
    lg: &LogicPrelude,
    rec: &RecordNames,
    large_indiscrete: NameId,
    group: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let group_ty = k.const_(group.ind, vec![]);
    let true_c = k.const_(lg.true_, vec![]);
    let li = k.const_(large_indiscrete, vec![]);
    let value = t_app(k, li, &[group_ty, prop, true_c]);
    let ty = k.const_(rec.ind, vec![]);

    let name = k.name_str(ns, "grpIndiscrete");
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
// Functors.
// ---------------------------------------------------------------------------

/// `CatS.idFunctor : forall (C : CatS.Category), CatS.Functor`.
fn declare_id_functor(
    k: &mut Kernel,
    cat: &RecordNames,
    func: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(C_FV);
    let c = cat_of(k, cat, cv);

    let fo = {
        let a = k.fvar(OA_FV);
        lam_over(k, OA_FV, c.obj, a)
    };
    let fm = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let hab = c.hom_ty(k, a, b);
        let f = k.fvar(MF_FV);
        let t = lam_over(k, MF_FV, hab, f);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };
    let map_congr = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let hab = c.hom_ty(k, a, b);
        let f = k.fvar(MF_FV);
        let g = k.fvar(MG_FV);
        let hyp = c.eqv(k, a, b, f, g);
        let h = k.fvar(HY1_FV);
        let t = lam_over(k, HY1_FV, hyp, h);
        let t = lam_over(k, MG_FV, hab, t);
        let t = lam_over(k, MF_FV, hab, t);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };
    let map_id = {
        let a = k.fvar(OA_FV);
        let ia = c.ident(k, a);
        let body = c.rfl(k, a, a, ia);
        lam_over(k, OA_FV, c.obj, body)
    };
    let map_comp = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let cc = k.fvar(OC_FV);
        let hbc = c.hom_ty(k, b, cc);
        let hab = c.hom_ty(k, a, b);
        let g = k.fvar(MG_FV);
        let f = k.fvar(MF_FV);
        let gf = c.cmp(k, a, b, cc, g, f);
        let body = c.rfl(k, a, cc, gf);
        let t = lam_over(k, MF_FV, hab, body);
        let t = lam_over(k, MG_FV, hbc, t);
        let t = lam_over(k, OC_FV, c.obj, t);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };

    let body = mk_instance(k, func, &[cv, cv, fo, fm, map_congr, map_id, map_comp]);
    let value = lam_over(k, C_FV, cat_ty, body);
    let func_ty = k.const_(func.ind, vec![]);
    let ty = pi_over(k, C_FV, cat_ty, func_ty);

    let name = k.name_str(ns, "idFunctor");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// The three hypothesis types a monoid homomorphism `h : M.carrier ->
/// N.carrier` carries: congruence, `op`-preservation, `e`-preservation.
struct MonHomTys {
    fn_ty: ExprId,
    congr: ExprId,
    op: ExprId,
    unit: ExprId,
}

fn mon_hom_tys(k: &mut Kernel, monoid: &RecordNames, m: ExprId, n: ExprId, h: ExprId) -> MonHomTys {
    use algs::monoid::{CARRIER, E, EQUIV, OP};
    let mc = sel(k, monoid, CARRIER, m);
    let nc = sel(k, monoid, CARRIER, n);
    let m_eq = sel(k, monoid, EQUIV, m);
    let n_eq = sel(k, monoid, EQUIV, n);
    let m_op = sel(k, monoid, OP, m);
    let n_op = sel(k, monoid, OP, n);
    let m_e = sel(k, monoid, E, m);
    let n_e = sel(k, monoid, E, n);
    let fn_ty = arrow(k, mc, nc);

    let a = k.fvar(EL_A_FV);
    let b = k.fvar(EL_B_FV);
    let hyp = app2(k, m_eq, a, b);
    let ha = k.app(h, a);
    let hb = k.app(h, b);
    let concl = app2(k, n_eq, ha, hb);
    let t = arrow(k, hyp, concl);
    let t = pi_over(k, EL_B_FV, mc, t);
    let congr = pi_over(k, EL_A_FV, mc, t);

    let a = k.fvar(EL_A_FV);
    let b = k.fvar(EL_B_FV);
    let ab = app2(k, m_op, a, b);
    let lhs = k.app(h, ab);
    let ha = k.app(h, a);
    let hb = k.app(h, b);
    let rhs = app2(k, n_op, ha, hb);
    let body = app2(k, n_eq, lhs, rhs);
    let t = pi_over(k, EL_B_FV, mc, body);
    let op = pi_over(k, EL_A_FV, mc, t);

    let hme = k.app(h, m_e);
    let unit = app2(k, n_eq, hme, n_e);

    MonHomTys {
        fn_ty,
        congr,
        op,
        unit,
    }
}

/// `CatS.ofMonoidHom` — a monoid homomorphism deloops to a **functor**, and
/// its three functoriality laws ARE the homomorphism's three laws. This is the
/// shape a forgetful functor would have if the categories it runs between were
/// expressible (they are not; see the module doc).
fn declare_of_monoid_hom(
    k: &mut Kernel,
    func: &RecordNames,
    monoid: &RecordNames,
    of_monoid: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use algs::monoid::CARRIER;
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sort1 = k.sort(l1);
    let mon_ty = k.const_(monoid.ind, vec![]);
    let a_ty = k.fvar(TA_FV);
    let m = k.fvar(MON_M_FV);
    let n = k.fvar(MON_N_FV);
    let h = k.fvar(FN_FV);
    let tys = mon_hom_tys(k, monoid, m, n, h);
    let mc = sel(k, monoid, CARRIER, m);

    let om = k.const_(of_monoid, vec![]);
    let src = t_app(k, om, &[a_ty, m]);
    let om2 = k.const_(of_monoid, vec![]);
    let tgt = t_app(k, om2, &[a_ty, n]);

    let fo = {
        let a = k.fvar(OA_FV);
        lam_over(k, OA_FV, a_ty, a)
    };
    let fm = {
        let f = k.fvar(MF_FV);
        let hf = k.app(h, f);
        let t = lam_over(k, MF_FV, mc, hf);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };
    // mapCongr := fun a b f g hfg => hCongr f g hfg
    let map_congr = {
        let hc = k.fvar(FCONGR_FV);
        let f = k.fvar(MF_FV);
        let g = k.fvar(MG_FV);
        let hh = k.fvar(HY1_FV);
        let applied = t_app(k, hc, &[f, g, hh]);
        let m_eq = {
            use algs::monoid::EQUIV;
            sel(k, monoid, EQUIV, m)
        };
        let hyp = app2(k, m_eq, f, g);
        let t = lam_over(k, HY1_FV, hyp, applied);
        let t = lam_over(k, MG_FV, mc, t);
        let t = lam_over(k, MF_FV, mc, t);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };
    // mapId := fun a => hE
    let map_id = {
        let he = k.fvar(FE_FV);
        lam_over(k, OA_FV, a_ty, he)
    };
    // mapComp := fun a b c g f => hOp g f
    let map_comp = {
        let ho = k.fvar(FOP_FV);
        let g = k.fvar(MG_FV);
        let f = k.fvar(MF_FV);
        let applied = t_app(k, ho, &[g, f]);
        let t = lam_over(k, MF_FV, mc, applied);
        let t = lam_over(k, MG_FV, mc, t);
        let t = lam_over(k, OC_FV, a_ty, t);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };

    let body = mk_instance(k, func, &[src, tgt, fo, fm, map_congr, map_id, map_comp]);
    let value = lam_over(k, FE_FV, tys.unit, body);
    let value = lam_over(k, FOP_FV, tys.op, value);
    let value = lam_over(k, FCONGR_FV, tys.congr, value);
    let value = lam_over(k, FN_FV, tys.fn_ty, value);
    let value = lam_over(k, MON_N_FV, mon_ty, value);
    let value = lam_over(k, MON_M_FV, mon_ty, value);
    let value = lam_over(k, TA_FV, sort1, value);

    let func_ty = k.const_(func.ind, vec![]);
    let ty = pi_over(k, FE_FV, tys.unit, func_ty);
    let ty = pi_over(k, FOP_FV, tys.op, ty);
    let ty = pi_over(k, FCONGR_FV, tys.congr, ty);
    let ty = pi_over(k, FN_FV, tys.fn_ty, ty);
    let ty = pi_over(k, MON_N_FV, mon_ty, ty);
    let ty = pi_over(k, MON_M_FV, mon_ty, ty);
    let ty = pi_over(k, TA_FV, sort1, ty);

    let name = k.name_str(ns, "ofMonoidHom");
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
// The unbundled predicates: `IsFunctor`, `IsNat`, `IsInitial`, `IsTerminal`.
// ---------------------------------------------------------------------------

/// `CatS.IsFunctor : forall (C D : Category) (Fo : C.obj -> D.obj)
///  (Fm : forall a b, C.hom a b -> D.hom (Fo a) (Fo b)), Prop` — the
/// **unbundled** twin of [`CatS.Functor`], in the style ADR-1609 used for
/// `AlgS.Module.IsModule`. Needed because composing two `Functor` RECORDS
/// would require `F.tgt` and `G.src` to be propositionally equal categories,
/// and this kernel would then have to transport along an `Eq` at `Sort 2`.
fn declare_is_functor(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    ns: NameId,
    suffix: &str,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(C_FV);
    let dv = k.fvar(D_FV);
    let c = cat_of(k, cat, cv);
    let d = cat_of(k, cat, dv);
    let fo_t = fo_ty(k, &c, &d);
    let fo = k.fvar(FO_FV);
    let fm_t = fm_ty(k, &c, &d, fo);
    let fm = k.fvar(FM_FV);

    let props = [
        functor_congr_stmt(k, &c, &d, fo, fm),
        functor_id_stmt(k, &c, &d, fo, fm),
        functor_comp_stmt(k, &c, &d, fo, fm),
    ];
    let body = and3(k, lg, &props);
    let value = lam_over(k, FM_FV, fm_t, body);
    let value = lam_over(k, FO_FV, fo_t, value);
    let value = lam_over(k, D_FV, cat_ty, value);
    let value = lam_over(k, C_FV, cat_ty, value);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = pi_over(k, FM_FV, fm_t, prop);
    let ty = pi_over(k, FO_FV, fo_t, ty);
    let ty = pi_over(k, D_FV, cat_ty, ty);
    let ty = pi_over(k, C_FV, cat_ty, ty);

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

/// The naturality square, up to the target's hom-equivalence:
/// `forall a b (f : C.hom a b), D.homEquiv (Fo a) (Go b)
///   (D.comp (eta b) (Fm a b f)) (D.comp (Gm a b f) (eta a))`.
#[allow(clippy::too_many_arguments)]
fn naturality_stmt(
    k: &mut Kernel,
    c: &Cat,
    d: &Cat,
    fo: ExprId,
    go: ExprId,
    fm: ExprId,
    gm: ExprId,
    eta: ExprId,
) -> ExprId {
    let a = k.fvar(OA_FV);
    let b = k.fvar(OB_FV);
    let hab = c.hom_ty(k, a, b);
    let f = k.fvar(MF_FV);
    let foa = k.app(fo, a);
    let fob = k.app(fo, b);
    let goa = k.app(go, a);
    let gob = k.app(go, b);
    let etab = k.app(eta, b);
    let etaa = k.app(eta, a);
    let fmf = t_app(k, fm, &[a, b, f]);
    let gmf = t_app(k, gm, &[a, b, f]);
    let lhs = d.cmp(k, foa, fob, gob, etab, fmf);
    let rhs = d.cmp(k, foa, goa, gob, gmf, etaa);
    let body = d.eqv(k, foa, gob, lhs, rhs);
    let t = pi_over(k, MF_FV, hab, body);
    let t = pi_over(k, OB_FV, c.obj, t);
    pi_over(k, OA_FV, c.obj, t)
}

/// `eta`'s type: `forall (a : C.obj), D.hom (Fo a) (Go a)`.
fn eta_ty(k: &mut Kernel, c: &Cat, d: &Cat, fo: ExprId, go: ExprId) -> ExprId {
    let a = k.fvar(OA_FV);
    let foa = k.app(fo, a);
    let goa = k.app(go, a);
    let body = d.hom_ty(k, foa, goa);
    pi_over(k, OA_FV, c.obj, body)
}

/// `CatS.IsNat` — a natural transformation as the naturality square alone.
/// Deliberately does NOT assume `Fm`/`Gm` functorial: naturality is a
/// statement about the square, and keeping the hypothesis list minimal is
/// part 1 of the universal-property template.
fn declare_is_nat(k: &mut Kernel, cat: &RecordNames, ns: NameId) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(C_FV);
    let dv = k.fvar(D_FV);
    let c = cat_of(k, cat, cv);
    let d = cat_of(k, cat, dv);
    let fo_t = fo_ty(k, &c, &d);
    let fo = k.fvar(FO_FV);
    let go = k.fvar(GO_FV);
    let fm_t = fm_ty(k, &c, &d, fo);
    let gm_t = fm_ty(k, &c, &d, go);
    let fm = k.fvar(FM_FV);
    let gm = k.fvar(GM_FV);
    let eta_t = eta_ty(k, &c, &d, fo, go);
    let eta = k.fvar(ETA_FV);

    let body = naturality_stmt(k, &c, &d, fo, go, fm, gm, eta);
    let value = lam_over(k, ETA_FV, eta_t, body);
    let value = lam_over(k, GM_FV, gm_t, value);
    let value = lam_over(k, FM_FV, fm_t, value);
    let value = lam_over(k, GO_FV, fo_t, value);
    let value = lam_over(k, FO_FV, fo_t, value);
    let value = lam_over(k, D_FV, cat_ty, value);
    let value = lam_over(k, C_FV, cat_ty, value);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = pi_over(k, ETA_FV, eta_t, prop);
    let ty = pi_over(k, GM_FV, gm_t, ty);
    let ty = pi_over(k, FM_FV, fm_t, ty);
    let ty = pi_over(k, GO_FV, fo_t, ty);
    let ty = pi_over(k, FO_FV, fo_t, ty);
    let ty = pi_over(k, D_FV, cat_ty, ty);
    let ty = pi_over(k, C_FV, cat_ty, ty);

    let name = k.name_str(ns, "IsNat");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `med`'s type for initiality: `forall (b : C.obj), C.hom a b`.
fn med_out_ty(k: &mut Kernel, c: &Cat, a: ExprId) -> ExprId {
    let b = k.fvar(OB_FV);
    let body = c.hom_ty(k, a, b);
    pi_over(k, OB_FV, c.obj, body)
}

/// `med`'s type for terminality: `forall (b : C.obj), C.hom b z`.
fn med_in_ty(k: &mut Kernel, c: &Cat, z: ExprId) -> ExprId {
    let b = k.fvar(OB_FV);
    let body = c.hom_ty(k, b, z);
    pi_over(k, OB_FV, c.obj, body)
}

/// `CatS.IsInitial C a med := forall b (g : C.hom a b), C.homEquiv a b (med b) g`
/// — the mediating map is **given**, not extracted from an `Exists`
/// (universal-property template, part 2), and uniqueness is up to the
/// hom-equivalence, which is the strongest form available without `funext`.
fn declare_is_initial(
    k: &mut Kernel,
    cat: &RecordNames,
    ns: NameId,
    dual: bool,
    suffix: &str,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(C_FV);
    let c = cat_of(k, cat, cv);
    let a = k.fvar(EL_A_FV);
    let med_t = if dual {
        med_in_ty(k, &c, a)
    } else {
        med_out_ty(k, &c, a)
    };
    let med = k.fvar(MED_A_FV);

    let b = k.fvar(OB_FV);
    let hom = if dual {
        c.hom_ty(k, b, a)
    } else {
        c.hom_ty(k, a, b)
    };
    let g = k.fvar(MG_FV);
    let medb = k.app(med, b);
    let body = if dual {
        c.eqv(k, b, a, medb, g)
    } else {
        c.eqv(k, a, b, medb, g)
    };
    let body = pi_over(k, MG_FV, hom, body);
    let body = pi_over(k, OB_FV, c.obj, body);

    let value = lam_over(k, MED_A_FV, med_t, body);
    let value = lam_over(k, EL_A_FV, c.obj, value);
    let value = lam_over(k, C_FV, cat_ty, value);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = pi_over(k, MED_A_FV, med_t, prop);
    let ty = pi_over(k, EL_A_FV, c.obj, ty);
    let ty = pi_over(k, C_FV, cat_ty, ty);

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

/// `CatS.IsGrpHom G H f := (forall a b, G.equiv a b -> H.equiv (f a) (f b))
///  ∧ (forall a b, H.equiv (f (G.op a b)) (H.op (f a) (f b)))` — the morphisms
/// of the category of groups, as a PREDICATE because the pair (function,
/// proof) cannot be a type here.
fn declare_is_grp_hom(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let (congr, op, fn_ty, g_ty) = grp_hom_parts(k, group, GRP_G_FV, GRP_H_FV, FN_FV);
    let and_c = k.const_(lg.and, vec![]);
    let body = app2(k, and_c, congr, op);
    let value = lam_over(k, FN_FV, fn_ty, body);
    let value = lam_over(k, GRP_H_FV, g_ty, value);
    let value = lam_over(k, GRP_G_FV, g_ty, value);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = pi_over(k, FN_FV, fn_ty, prop);
    let ty = pi_over(k, GRP_H_FV, g_ty, ty);
    let ty = pi_over(k, GRP_G_FV, g_ty, ty);

    let name = k.name_str(ns, "IsGrpHom");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `(congr statement, op statement, f's type, AlgS.Group)` for `f : G -> H`
/// with `G` at `g_fv`, `H` at `h_fv`, `f` at `f_fv`.
fn grp_hom_parts(
    k: &mut Kernel,
    group: &RecordNames,
    g_fv: u64,
    h_fv: u64,
    f_fv: u64,
) -> (ExprId, ExprId, ExprId, ExprId) {
    use algs::group::{CARRIER, EQUIV, OP};
    let g_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(g_fv);
    let h = k.fvar(h_fv);
    let gc = sel(k, group, CARRIER, g);
    let hc = sel(k, group, CARRIER, h);
    let g_eq = sel(k, group, EQUIV, g);
    let h_eq = sel(k, group, EQUIV, h);
    let g_op = sel(k, group, OP, g);
    let h_op = sel(k, group, OP, h);
    let f = k.fvar(f_fv);
    let fn_ty = arrow(k, gc, hc);

    let a = k.fvar(EL_A_FV);
    let b = k.fvar(EL_B_FV);
    let hyp = app2(k, g_eq, a, b);
    let fa = k.app(f, a);
    let fb = k.app(f, b);
    let concl = app2(k, h_eq, fa, fb);
    let t = arrow(k, hyp, concl);
    let t = pi_over(k, EL_B_FV, gc, t);
    let congr = pi_over(k, EL_A_FV, gc, t);

    let a = k.fvar(EL_A_FV);
    let b = k.fvar(EL_B_FV);
    let ab = app2(k, g_op, a, b);
    let lhs = k.app(f, ab);
    let fa = k.app(f, a);
    let fb = k.app(f, b);
    let rhs = app2(k, h_op, fa, fb);
    let body = app2(k, h_eq, lhs, rhs);
    let t = pi_over(k, EL_B_FV, gc, body);
    let op = pi_over(k, EL_A_FV, gc, t);

    (congr, op, fn_ty, g_ty)
}

// ---------------------------------------------------------------------------
// Theorems.
// ---------------------------------------------------------------------------

fn thm(
    k: &mut Kernel,
    ns: NameId,
    suffix: &str,
    ty: ExprId,
    value: ExprId,
) -> Result<NameId, KernelError> {
    let name = k.name_str(ns, suffix);
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `CatS.functor_isFunctor : forall (F : Functor), IsFunctor F.src F.tgt
///  F.obj F.map` — the bundled record satisfies the unbundled predicate.
fn declare_functor_is_functor(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    func: &RecordNames,
    is_functor: NameId,
    ns: NameId,
    suffix: &str,
) -> Result<NameId, KernelError> {
    use idx::functor::{MAP, MAP_COMP, MAP_CONGR, MAP_ID, OBJ as F_OBJ, SRC, TGT};
    let func_ty = k.const_(func.ind, vec![]);
    let fv = k.fvar(FUNC_FV);
    let src = sel(k, func, SRC, fv);
    let tgt = sel(k, func, TGT, fv);
    let fo = sel(k, func, F_OBJ, fv);
    let fm = sel(k, func, MAP, fv);
    let c = cat_of(k, cat, src);
    let d = cat_of(k, cat, tgt);
    let props = [
        functor_congr_stmt(k, &c, &d, fo, fm),
        functor_id_stmt(k, &c, &d, fo, fm),
        functor_comp_stmt(k, &c, &d, fo, fm),
    ];
    let vals = [
        sel(k, func, MAP_CONGR, fv),
        sel(k, func, MAP_ID, fv),
        sel(k, func, MAP_COMP, fv),
    ];
    let value = intro3(k, lg, &props, &vals);
    let value = lam_over(k, FUNC_FV, func_ty, value);

    let isf = k.const_(is_functor, vec![]);
    let body = t_app(k, isf, &[src, tgt, fo, fm]);
    let ty = pi_over(k, FUNC_FV, func_ty, body);

    thm(k, ns, suffix, ty, value)
}

/// `CatS.isFunctor_id : forall (C : Category), IsFunctor C C (fun a => a)
///  (fun a b f => f)`.
fn declare_is_functor_id(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    is_functor: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(C_FV);
    let c = cat_of(k, cat, cv);
    let fo = {
        let a = k.fvar(OA_FV);
        lam_over(k, OA_FV, c.obj, a)
    };
    let fm = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let hab = c.hom_ty(k, a, b);
        let f = k.fvar(MF_FV);
        let t = lam_over(k, MF_FV, hab, f);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };
    let props = [
        functor_congr_stmt(k, &c, &c, fo, fm),
        functor_id_stmt(k, &c, &c, fo, fm),
        functor_comp_stmt(k, &c, &c, fo, fm),
    ];
    let v_congr = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let hab = c.hom_ty(k, a, b);
        let f = k.fvar(MF_FV);
        let g = k.fvar(MG_FV);
        let hyp = c.eqv(k, a, b, f, g);
        let hh = k.fvar(HY1_FV);
        let t = lam_over(k, HY1_FV, hyp, hh);
        let t = lam_over(k, MG_FV, hab, t);
        let t = lam_over(k, MF_FV, hab, t);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };
    let v_id = {
        let a = k.fvar(OA_FV);
        let ia = c.ident(k, a);
        let body = c.rfl(k, a, a, ia);
        lam_over(k, OA_FV, c.obj, body)
    };
    let v_comp = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let cc = k.fvar(OC_FV);
        let hbc = c.hom_ty(k, b, cc);
        let hab = c.hom_ty(k, a, b);
        let g = k.fvar(MG_FV);
        let f = k.fvar(MF_FV);
        let gf = c.cmp(k, a, b, cc, g, f);
        let body = c.rfl(k, a, cc, gf);
        let t = lam_over(k, MF_FV, hab, body);
        let t = lam_over(k, MG_FV, hbc, t);
        let t = lam_over(k, OC_FV, c.obj, t);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };
    let value = intro3(k, lg, &props, &[v_congr, v_id, v_comp]);
    let value = lam_over(k, C_FV, cat_ty, value);

    let isf = k.const_(is_functor, vec![]);
    let body = t_app(k, isf, &[cv, cv, fo, fm]);
    let ty = pi_over(k, C_FV, cat_ty, body);

    thm(k, ns, "isFunctor_id", ty, value)
}

/// `CatS.isFunctor_comp` — functors compose. The composition law of the
/// category of categories, and the reason [`CatS.IsFunctor`] exists as a
/// predicate rather than only as the record.
#[allow(clippy::too_many_lines)]
fn declare_is_functor_comp(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    is_functor: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(C_FV);
    let dv = k.fvar(D_FV);
    let ev = k.fvar(E_FV);
    let c = cat_of(k, cat, cv);
    let d = cat_of(k, cat, dv);
    let e = cat_of(k, cat, ev);

    let fo_t = fo_ty(k, &c, &d);
    let fo = k.fvar(FO_FV);
    let fm_t = fm_ty(k, &c, &d, fo);
    let fm = k.fvar(FM_FV);
    let go_t = fo_ty(k, &d, &e);
    let go = k.fvar(GO_FV);
    let gm_t = fm_ty(k, &d, &e, go);
    let gm = k.fvar(GM_FV);

    let f_props = [
        functor_congr_stmt(k, &c, &d, fo, fm),
        functor_id_stmt(k, &c, &d, fo, fm),
        functor_comp_stmt(k, &c, &d, fo, fm),
    ];
    let g_props = [
        functor_congr_stmt(k, &d, &e, go, gm),
        functor_id_stmt(k, &d, &e, go, gm),
        functor_comp_stmt(k, &d, &e, go, gm),
    ];
    let isf = k.const_(is_functor, vec![]);
    let f_hyp = t_app(k, isf, &[cv, dv, fo, fm]);
    let isf2 = k.const_(is_functor, vec![]);
    let g_hyp = t_app(k, isf2, &[dv, ev, go, gm]);
    let hf = k.fvar(HIA_FV);
    let hg = k.fvar(HIB_FV);

    // The composite's object and morphism maps.
    let ho = {
        let a = k.fvar(OA_FV);
        let foa = k.app(fo, a);
        let body = k.app(go, foa);
        lam_over(k, OA_FV, c.obj, body)
    };
    let hm = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let hab = c.hom_ty(k, a, b);
        let f = k.fvar(MF_FV);
        let foa = k.app(fo, a);
        let fob = k.app(fo, b);
        let fmf = t_app(k, fm, &[a, b, f]);
        let body = t_app(k, gm, &[foa, fob, fmf]);
        let t = lam_over(k, MF_FV, hab, body);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };

    let f_congr = project3(k, lg, &f_props, hf, 0);
    let f_id = project3(k, lg, &f_props, hf, 1);
    let f_comp = project3(k, lg, &f_props, hf, 2);
    let g_congr = project3(k, lg, &g_props, hg, 0);
    let g_id = project3(k, lg, &g_props, hg, 1);
    let g_comp = project3(k, lg, &g_props, hg, 2);

    // 1. congruence: `gc (Fo a) (Fo b) _ _ (fc a b f g h)`.
    let v_congr = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let hab = c.hom_ty(k, a, b);
        let f = k.fvar(MF_FV);
        let g = k.fvar(MG_FV);
        let hyp = c.eqv(k, a, b, f, g);
        let hh = k.fvar(HY1_FV);
        let inner = t_app(k, f_congr, &[a, b, f, g, hh]);
        let foa = k.app(fo, a);
        let fob = k.app(fo, b);
        let fmf = t_app(k, fm, &[a, b, f]);
        let fmg = t_app(k, fm, &[a, b, g]);
        let body = t_app(k, g_congr, &[foa, fob, fmf, fmg, inner]);
        let t = lam_over(k, HY1_FV, hyp, body);
        let t = lam_over(k, MG_FV, hab, t);
        let t = lam_over(k, MF_FV, hab, t);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };

    // 2. identities: trans (gc _ _ _ _ (fId a)) (gId (Fo a)).
    let v_id = {
        let a = k.fvar(OA_FV);
        let foa = k.app(fo, a);
        let goa = k.app(go, foa);
        let ia = c.ident(k, a);
        let fm_ia = t_app(k, fm, &[a, a, ia]);
        let d_id = d.ident(k, foa);
        let fid = k.app(f_id, a);
        // `E.homEquiv (Go (Fo a)) (Go (Fo a)) (Gm _ _ (Fm a a (id a))) (Gm _ _ (D.id (Fo a)))`
        let step1 = t_app(k, g_congr, &[foa, foa, fm_ia, d_id, fid]);
        let step2 = k.app(g_id, foa);
        let x = t_app(k, gm, &[foa, foa, fm_ia]);
        let y = t_app(k, gm, &[foa, foa, d_id]);
        let z = e.ident(k, goa);
        let body = e.tr(k, goa, goa, x, y, z, step1, step2);
        lam_over(k, OA_FV, c.obj, body)
    };

    // 3. composition: trans (gc _ _ _ _ (fComp …)) (gComp …).
    let v_comp = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let cc = k.fvar(OC_FV);
        let hbc = c.hom_ty(k, b, cc);
        let hab = c.hom_ty(k, a, b);
        let g = k.fvar(MG_FV);
        let f = k.fvar(MF_FV);
        let foa = k.app(fo, a);
        let fob = k.app(fo, b);
        let foc = k.app(fo, cc);
        let goa = k.app(go, foa);
        let goc = k.app(go, foc);
        let gf = c.cmp(k, a, b, cc, g, f);
        let fm_gf = t_app(k, fm, &[a, cc, gf]);
        let fmg = t_app(k, fm, &[b, cc, g]);
        let fmf = t_app(k, fm, &[a, b, f]);
        let d_comp = d.cmp(k, foa, fob, foc, fmg, fmf);
        let fcomp = t_app(k, f_comp, &[a, b, cc, g, f]);
        let step1 = t_app(k, g_congr, &[foa, foc, fm_gf, d_comp, fcomp]);
        let step2 = t_app(k, g_comp, &[foa, fob, foc, fmg, fmf]);
        let x = t_app(k, gm, &[foa, foc, fm_gf]);
        let y = t_app(k, gm, &[foa, foc, d_comp]);
        let gob = k.app(go, fob);
        let gm_g = t_app(k, gm, &[fob, foc, fmg]);
        let gm_f = t_app(k, gm, &[foa, fob, fmf]);
        let z = e.cmp(k, goa, gob, goc, gm_g, gm_f);
        let body = e.tr(k, goa, goc, x, y, z, step1, step2);
        let t = lam_over(k, MF_FV, hab, body);
        let t = lam_over(k, MG_FV, hbc, t);
        let t = lam_over(k, OC_FV, c.obj, t);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };

    let h_props = [
        functor_congr_stmt(k, &c, &e, ho, hm),
        functor_id_stmt(k, &c, &e, ho, hm),
        functor_comp_stmt(k, &c, &e, ho, hm),
    ];
    let value = intro3(k, lg, &h_props, &[v_congr, v_id, v_comp]);
    let value = lam_over(k, HIB_FV, g_hyp, value);
    let value = lam_over(k, HIA_FV, f_hyp, value);
    let value = lam_over(k, GM_FV, gm_t, value);
    let value = lam_over(k, GO_FV, go_t, value);
    let value = lam_over(k, FM_FV, fm_t, value);
    let value = lam_over(k, FO_FV, fo_t, value);
    let value = lam_over(k, E_FV, cat_ty, value);
    let value = lam_over(k, D_FV, cat_ty, value);
    let value = lam_over(k, C_FV, cat_ty, value);

    let isf3 = k.const_(is_functor, vec![]);
    let concl = t_app(k, isf3, &[cv, ev, ho, hm]);
    let ty = arrow(k, g_hyp, concl);
    let ty = arrow(k, f_hyp, ty);
    let ty = pi_over(k, GM_FV, gm_t, ty);
    let ty = pi_over(k, GO_FV, go_t, ty);
    let ty = pi_over(k, FM_FV, fm_t, ty);
    let ty = pi_over(k, FO_FV, fo_t, ty);
    let ty = pi_over(k, E_FV, cat_ty, ty);
    let ty = pi_over(k, D_FV, cat_ty, ty);
    let ty = pi_over(k, C_FV, cat_ty, ty);

    thm(k, ns, "isFunctor_comp", ty, value)
}

/// `CatS.isNat_id : forall C, IsNat C C id id id id (fun a => C.id a)` — the
/// identity natural transformation. Its naturality square is exactly
/// `idL` followed by the symmetric `idR`, which is the smallest possible
/// demonstration that the square is a hom-EQUIVALENCE statement and not an
/// equation.
fn declare_is_nat_id(
    k: &mut Kernel,
    cat: &RecordNames,
    is_nat: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(C_FV);
    let c = cat_of(k, cat, cv);
    let fo = {
        let a = k.fvar(OA_FV);
        lam_over(k, OA_FV, c.obj, a)
    };
    let fm = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let hab = c.hom_ty(k, a, b);
        let f = k.fvar(MF_FV);
        let t = lam_over(k, MF_FV, hab, f);
        let t = lam_over(k, OB_FV, c.obj, t);
        lam_over(k, OA_FV, c.obj, t)
    };
    let eta = {
        let a = k.fvar(OA_FV);
        let ia = c.ident(k, a);
        lam_over(k, OA_FV, c.obj, ia)
    };

    let value = {
        let a = k.fvar(OA_FV);
        let b = k.fvar(OB_FV);
        let hab = c.hom_ty(k, a, b);
        let f = k.fvar(MF_FV);
        let ib = c.ident(k, b);
        let ia = c.ident(k, a);
        let lhs = c.cmp(k, a, b, b, ib, f);
        let rhs = c.cmp(k, a, a, b, f, ia);
        let idl = sel(k, cat, ID_L, cv);
        let h1 = t_app(k, idl, &[a, b, f]);
        let idr = sel(k, cat, ID_R, cv);
        let h2raw = t_app(k, idr, &[a, b, f]);
        let h2 = c.sy(k, a, b, rhs, f, h2raw);
        let body = c.tr(k, a, b, lhs, f, rhs, h1, h2);
        let t = lam_over(k, MF_FV, hab, body);
        let t = lam_over(k, OB_FV, c.obj, t);
        let t = lam_over(k, OA_FV, c.obj, t);
        lam_over(k, C_FV, cat_ty, t)
    };

    let isn = k.const_(is_nat, vec![]);
    let body = t_app(k, isn, &[cv, cv, fo, fo, fm, fm, eta]);
    let ty = pi_over(k, C_FV, cat_ty, body);

    thm(k, ns, "isNat_id", ty, value)
}

/// `CatS.isNat_ofMonoid` — between two deloopings of monoid maps `h`, `h'`,
/// a natural transformation is exactly an **intertwiner**: an element `n` with
/// `n · h x ~ h' x · n` for every `x`. The naturality square IS that
/// condition, so the theorem is the hypothesis, applied.
fn declare_is_nat_of_monoid(
    k: &mut Kernel,
    monoid: &RecordNames,
    of_monoid: NameId,
    is_nat: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use algs::monoid::{CARRIER, EQUIV, OP};
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sort1 = k.sort(l1);
    let mon_ty = k.const_(monoid.ind, vec![]);
    let a_ty = k.fvar(TA_FV);
    let m = k.fvar(MON_M_FV);
    let n = k.fvar(MON_N_FV);
    let mc = sel(k, monoid, CARRIER, m);
    let nc = sel(k, monoid, CARRIER, n);
    let n_eq = sel(k, monoid, EQUIV, n);
    let n_op = sel(k, monoid, OP, n);
    let fn_ty = arrow(k, mc, nc);
    let h = k.fvar(FN_FV);
    let h2 = k.fvar(FN2_FV);
    let elt = k.fvar(EL_N_FV);

    // `forall x, N.equiv (N.op n (h x)) (N.op (h' x) n)`
    let inter_ty = {
        let x = k.fvar(EL_A_FV);
        let hx = k.app(h, x);
        let h2x = k.app(h2, x);
        let lhs = app2(k, n_op, elt, hx);
        let rhs = app2(k, n_op, h2x, elt);
        let body = app2(k, n_eq, lhs, rhs);
        pi_over(k, EL_A_FV, mc, body)
    };
    let inter = k.fvar(HY1_FV);

    let om = k.const_(of_monoid, vec![]);
    let src = t_app(k, om, &[a_ty, m]);
    let om2 = k.const_(of_monoid, vec![]);
    let tgt = t_app(k, om2, &[a_ty, n]);

    let fo = {
        let a = k.fvar(OA_FV);
        lam_over(k, OA_FV, a_ty, a)
    };
    let mk_map = |k: &mut Kernel, hh: ExprId| -> ExprId {
        let f = k.fvar(MF_FV);
        let applied = k.app(hh, f);
        let t = lam_over(k, MF_FV, mc, applied);
        let t = lam_over(k, OB_FV, a_ty, t);
        lam_over(k, OA_FV, a_ty, t)
    };
    let fm = mk_map(k, h);
    let gm = mk_map(k, h2);
    let eta = lam_over(k, OA_FV, a_ty, elt);

    // `fun a b f => inter f`
    let value = {
        let f = k.fvar(MF_FV);
        let applied = k.app(inter, f);
        let t = lam_over(k, MF_FV, mc, applied);
        let t = lam_over(k, OB_FV, a_ty, t);
        let t = lam_over(k, OA_FV, a_ty, t);
        let t = lam_over(k, HY1_FV, inter_ty, t);
        let t = lam_over(k, EL_N_FV, nc, t);
        let t = lam_over(k, FN2_FV, fn_ty, t);
        let t = lam_over(k, FN_FV, fn_ty, t);
        let t = lam_over(k, MON_N_FV, mon_ty, t);
        let t = lam_over(k, MON_M_FV, mon_ty, t);
        lam_over(k, TA_FV, sort1, t)
    };

    let isn = k.const_(is_nat, vec![]);
    let concl = t_app(k, isn, &[src, tgt, fo, fo, fm, gm, eta]);
    let ty = pi_over(k, HY1_FV, inter_ty, concl);
    let ty = pi_over(k, EL_N_FV, nc, ty);
    let ty = pi_over(k, FN2_FV, fn_ty, ty);
    let ty = pi_over(k, FN_FV, fn_ty, ty);
    let ty = pi_over(k, MON_N_FV, mon_ty, ty);
    let ty = pi_over(k, MON_M_FV, mon_ty, ty);
    let ty = pi_over(k, TA_FV, sort1, ty);

    thm(k, ns, "isNat_ofMonoid", ty, value)
}

/// `CatS.initial_unique` — two initial objects are isomorphic, both round
/// trips equivalent to the identity. The theorem the universal-property
/// template's two carriers each prove by hand.
fn declare_initial_unique(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    is_initial: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(C_FV);
    let c = cat_of(k, cat, cv);
    let a = k.fvar(EL_A_FV);
    let b = k.fvar(EL_B_FV);
    let med_a_t = med_out_ty(k, &c, a);
    let med_b_t = med_out_ty(k, &c, b);
    let med_a = k.fvar(MED_A_FV);
    let med_b = k.fvar(MED_B_FV);
    let isi = k.const_(is_initial, vec![]);
    let ha_ty = t_app(k, isi, &[cv, a, med_a]);
    let isi2 = k.const_(is_initial, vec![]);
    let hb_ty = t_app(k, isi2, &[cv, b, med_b]);
    let ha = k.fvar(HIA_FV);
    let hb = k.fvar(HIB_FV);

    let med_a_b = k.app(med_a, b);
    let med_b_a = k.app(med_b, a);
    let med_a_a = k.app(med_a, a);
    let med_b_b = k.app(med_b, b);
    let round_a = c.cmp(k, a, b, a, med_b_a, med_a_b);
    let round_b = c.cmp(k, b, a, b, med_a_b, med_b_a);
    let id_a = c.ident(k, a);
    let id_b = c.ident(k, b);

    let p1 = c.eqv(k, a, a, round_a, id_a);
    let p2 = c.eqv(k, b, b, round_b, id_b);
    let and_c = k.const_(lg.and, vec![]);
    let concl = app2(k, and_c, p1, p2);

    // proof of p1: trans (symm (ha a round_a)) (ha a (id a))
    let u1 = t_app(k, ha, &[a, round_a]);
    let v1 = c.sy(k, a, a, med_a_a, round_a, u1);
    let w1 = t_app(k, ha, &[a, id_a]);
    let pf1 = c.tr(k, a, a, round_a, med_a_a, id_a, v1, w1);
    let u2 = t_app(k, hb, &[b, round_b]);
    let v2 = c.sy(k, b, b, med_b_b, round_b, u2);
    let w2 = t_app(k, hb, &[b, id_b]);
    let pf2 = c.tr(k, b, b, round_b, med_b_b, id_b, v2, w2);
    let ai = k.const_(lg.and_intro, vec![]);
    let value = t_app(k, ai, &[p1, p2, pf1, pf2]);

    let value = lam_over(k, HIB_FV, hb_ty, value);
    let value = lam_over(k, HIA_FV, ha_ty, value);
    let value = lam_over(k, MED_B_FV, med_b_t, value);
    let value = lam_over(k, EL_B_FV, c.obj, value);
    let value = lam_over(k, MED_A_FV, med_a_t, value);
    let value = lam_over(k, EL_A_FV, c.obj, value);
    let value = lam_over(k, C_FV, cat_ty, value);

    let ty = arrow(k, hb_ty, concl);
    let ty = arrow(k, ha_ty, ty);
    let ty = pi_over(k, MED_B_FV, med_b_t, ty);
    let ty = pi_over(k, EL_B_FV, c.obj, ty);
    let ty = pi_over(k, MED_A_FV, med_a_t, ty);
    let ty = pi_over(k, EL_A_FV, c.obj, ty);
    let ty = pi_over(k, C_FV, cat_ty, ty);

    thm(k, ns, "initial_unique", ty, value)
}

/// `CatS.indiscrete_isInitial` / `CatS.indiscrete_isTerminal` — every object
/// of the indiscrete category is both initial and terminal.
fn declare_indiscrete_universal(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    indiscrete: NameId,
    pred: NameId,
    ns: NameId,
    dual: bool,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sort1 = k.sort(l1);
    let a_ty = k.fvar(TA_FV);
    let ind = k.const_(indiscrete, vec![]);
    let cv = k.app(ind, a_ty);
    let c = cat_of(k, cat, cv);
    let a = k.fvar(EL_A_FV);

    let med = lam_over(k, OB_FV, c.obj, a);
    let ti = k.const_(lg.true_intro, vec![]);

    let b = k.fvar(OB_FV);
    let hom = if dual {
        c.hom_ty(k, b, a)
    } else {
        c.hom_ty(k, a, b)
    };
    let value = {
        let t = lam_over(k, MG_FV, hom, ti);
        let t = lam_over(k, OB_FV, c.obj, t);
        let t = lam_over(k, EL_A_FV, c.obj, t);
        lam_over(k, TA_FV, sort1, t)
    };

    let p = k.const_(pred, vec![]);
    let concl = t_app(k, p, &[cv, a, med]);
    let ty = pi_over(k, EL_A_FV, c.obj, concl);
    let ty = pi_over(k, TA_FV, sort1, ty);

    thm(
        k,
        ns,
        if dual {
            "indiscrete_isTerminal"
        } else {
            "indiscrete_isInitial"
        },
        ty,
        value,
    )
}

/// `CatS.isGrpHom_id : forall (G : AlgS.Group), IsGrpHom G G (fun a => a)`.
fn declare_is_grp_hom_id(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    is_grp_hom: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use algs::group::{CARRIER, EQUIV_REFL, OP};
    let g_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(GRP_G_FV);
    let gc = sel(k, group, CARRIER, g);
    let g_op = sel(k, group, OP, g);
    let g_refl = sel(k, group, EQUIV_REFL, g);
    let idf = {
        let a = k.fvar(EL_A_FV);
        lam_over(k, EL_A_FV, gc, a)
    };
    let igh = k.const_(is_grp_hom, vec![]);
    let concl = t_app(k, igh, &[g, g, idf]);
    let ty = pi_over(k, GRP_G_FV, g_ty, concl);

    // The two conjuncts, as `IsGrpHom G G (fun a => a)` beta-reduces to them.
    let g_eq = {
        use algs::group::EQUIV;
        sel(k, group, EQUIV, g)
    };
    let congr_p = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let hyp = app2(k, g_eq, a, b);
        let cl = app2(k, g_eq, a, b);
        let t = arrow(k, hyp, cl);
        let t = pi_over(k, EL_B_FV, gc, t);
        pi_over(k, EL_A_FV, gc, t)
    };
    let op_p = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let ab = app2(k, g_op, a, b);
        let body = app2(k, g_eq, ab, ab);
        let t = pi_over(k, EL_B_FV, gc, body);
        pi_over(k, EL_A_FV, gc, t)
    };

    let v_congr = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let hyp = app2(k, g_eq, a, b);
        let hh = k.fvar(HY1_FV);
        let t = lam_over(k, HY1_FV, hyp, hh);
        let t = lam_over(k, EL_B_FV, gc, t);
        lam_over(k, EL_A_FV, gc, t)
    };
    let v_op = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let ab = app2(k, g_op, a, b);
        let body = k.app(g_refl, ab);
        let t = lam_over(k, EL_B_FV, gc, body);
        lam_over(k, EL_A_FV, gc, t)
    };
    let ai = k.const_(lg.and_intro, vec![]);
    let value = t_app(k, ai, &[congr_p, op_p, v_congr, v_op]);
    let value = lam_over(k, GRP_G_FV, g_ty, value);

    thm(k, ns, "isGrpHom_id", ty, value)
}

/// `CatS.isGrpHom_comp` — group homomorphisms compose. With
/// [`CatS.isGrpHom_id`] these are the identity and composition laws of the
/// category of groups, stated without the `Sigma` that would bundle them.
fn declare_is_grp_hom_comp(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    is_grp_hom: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    use algs::group::{CARRIER, EQUIV, EQUIV_TRANS, OP};
    let g_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(GRP_G_FV);
    let h = k.fvar(GRP_H_FV);
    let kk = k.fvar(GRP_K_FV);
    let gc = sel(k, group, CARRIER, g);
    let hc = sel(k, group, CARRIER, h);
    let kc = sel(k, group, CARRIER, kk);
    let g_eq = sel(k, group, EQUIV, g);
    let h_eq = sel(k, group, EQUIV, h);
    let k_eq = sel(k, group, EQUIV, kk);
    let g_op = sel(k, group, OP, g);
    let h_op = sel(k, group, OP, h);
    let k_op = sel(k, group, OP, kk);
    let k_trans = sel(k, group, EQUIV_TRANS, kk);

    let f_ty = arrow(k, gc, hc);
    let g2_ty = arrow(k, hc, kc);
    let f = k.fvar(FN_FV);
    let g2 = k.fvar(FN2_FV);

    let igh = k.const_(is_grp_hom, vec![]);
    let hf_ty = t_app(k, igh, &[g, h, f]);
    let igh2 = k.const_(is_grp_hom, vec![]);
    let hg_ty = t_app(k, igh2, &[h, kk, g2]);
    let hf = k.fvar(HIA_FV);
    let hg = k.fvar(HIB_FV);

    // The composite.
    let comp_fn = {
        let a = k.fvar(EL_A_FV);
        let fa = k.app(f, a);
        let body = k.app(g2, fa);
        lam_over(k, EL_A_FV, gc, body)
    };

    // `f`'s two conjuncts (as stated by `IsGrpHom G H f`).
    let f_congr_p = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let hyp = app2(k, g_eq, a, b);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let cl = app2(k, h_eq, fa, fb);
        let t = arrow(k, hyp, cl);
        let t = pi_over(k, EL_B_FV, gc, t);
        pi_over(k, EL_A_FV, gc, t)
    };
    let f_op_p = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let ab = app2(k, g_op, a, b);
        let lhs = k.app(f, ab);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let rhs = app2(k, h_op, fa, fb);
        let body = app2(k, h_eq, lhs, rhs);
        let t = pi_over(k, EL_B_FV, gc, body);
        pi_over(k, EL_A_FV, gc, t)
    };
    let g_congr_p = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let hyp = app2(k, h_eq, a, b);
        let ga = k.app(g2, a);
        let gb = k.app(g2, b);
        let cl = app2(k, k_eq, ga, gb);
        let t = arrow(k, hyp, cl);
        let t = pi_over(k, EL_B_FV, hc, t);
        pi_over(k, EL_A_FV, hc, t)
    };
    let g_op_p = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let ab = app2(k, h_op, a, b);
        let lhs = k.app(g2, ab);
        let ga = k.app(g2, a);
        let gb = k.app(g2, b);
        let rhs = app2(k, k_op, ga, gb);
        let body = app2(k, k_eq, lhs, rhs);
        let t = pi_over(k, EL_B_FV, hc, body);
        pi_over(k, EL_A_FV, hc, t)
    };

    let al = k.const_(lg.and_left, vec![]);
    let hf_congr = t_app(k, al, &[f_congr_p, f_op_p, hf]);
    let ar = k.const_(lg.and_right, vec![]);
    let hf_op = t_app(k, ar, &[f_congr_p, f_op_p, hf]);
    let al2 = k.const_(lg.and_left, vec![]);
    let hg_congr = t_app(k, al2, &[g_congr_p, g_op_p, hg]);
    let ar2 = k.const_(lg.and_right, vec![]);
    let hg_op = t_app(k, ar2, &[g_congr_p, g_op_p, hg]);

    // Conjunct 1: `fun a b hab => gCongr (f a) (f b) (fCongr a b hab)`.
    let v_congr = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let hyp = app2(k, g_eq, a, b);
        let hh = k.fvar(HY1_FV);
        let inner = t_app(k, hf_congr, &[a, b, hh]);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let body = t_app(k, hg_congr, &[fa, fb, inner]);
        let t = lam_over(k, HY1_FV, hyp, body);
        let t = lam_over(k, EL_B_FV, gc, t);
        lam_over(k, EL_A_FV, gc, t)
    };
    // Conjunct 2: trans (gCongr _ _ (fOp a b)) (gOp (f a) (f b)).
    let v_op = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let ab = app2(k, g_op, a, b);
        let f_ab = k.app(f, ab);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let h_fa_fb = app2(k, h_op, fa, fb);
        let fop_ab = t_app(k, hf_op, &[a, b]);
        let step1 = t_app(k, hg_congr, &[f_ab, h_fa_fb, fop_ab]);
        let step2 = t_app(k, hg_op, &[fa, fb]);
        let x = k.app(g2, f_ab);
        let y = k.app(g2, h_fa_fb);
        let ga = k.app(g2, fa);
        let gb = k.app(g2, fb);
        let z = app2(k, k_op, ga, gb);
        let body = t_app(k, k_trans, &[x, y, z, step1, step2]);
        let t = lam_over(k, EL_B_FV, gc, body);
        lam_over(k, EL_A_FV, gc, t)
    };

    // The composite's own two conjuncts.
    let c_congr_p = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let hyp = app2(k, g_eq, a, b);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let ga = k.app(g2, fa);
        let gb = k.app(g2, fb);
        let cl = app2(k, k_eq, ga, gb);
        let t = arrow(k, hyp, cl);
        let t = pi_over(k, EL_B_FV, gc, t);
        pi_over(k, EL_A_FV, gc, t)
    };
    let c_op_p = {
        let a = k.fvar(EL_A_FV);
        let b = k.fvar(EL_B_FV);
        let ab = app2(k, g_op, a, b);
        let f_ab = k.app(f, ab);
        let lhs = k.app(g2, f_ab);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let ga = k.app(g2, fa);
        let gb = k.app(g2, fb);
        let rhs = app2(k, k_op, ga, gb);
        let body = app2(k, k_eq, lhs, rhs);
        let t = pi_over(k, EL_B_FV, gc, body);
        pi_over(k, EL_A_FV, gc, t)
    };
    let ai = k.const_(lg.and_intro, vec![]);
    let value = t_app(k, ai, &[c_congr_p, c_op_p, v_congr, v_op]);
    let value = lam_over(k, HIB_FV, hg_ty, value);
    let value = lam_over(k, HIA_FV, hf_ty, value);
    let value = lam_over(k, FN2_FV, g2_ty, value);
    let value = lam_over(k, FN_FV, f_ty, value);
    let value = lam_over(k, GRP_K_FV, g_ty, value);
    let value = lam_over(k, GRP_H_FV, g_ty, value);
    let value = lam_over(k, GRP_G_FV, g_ty, value);

    let igh3 = k.const_(is_grp_hom, vec![]);
    let concl = t_app(k, igh3, &[g, kk, comp_fn]);
    let ty = arrow(k, hg_ty, concl);
    let ty = arrow(k, hf_ty, ty);
    let ty = pi_over(k, FN2_FV, g2_ty, ty);
    let ty = pi_over(k, FN_FV, f_ty, ty);
    let ty = pi_over(k, GRP_K_FV, g_ty, ty);
    let ty = pi_over(k, GRP_H_FV, g_ty, ty);
    let ty = pi_over(k, GRP_G_FV, g_ty, ty);

    thm(k, ns, "isGrpHom_comp", ty, value)
}

// ---------------------------------------------------------------------------
// The entry point.
// ---------------------------------------------------------------------------

/// Declare the whole `CatS.*` layer. Needs only [`LogicPrelude`] and the
/// `AlgS.Monoid` / `AlgS.Group` records, so it lands at the `AlgS` build
/// position alongside `AlgS.Poly.*`, `AlgS.Module.*` and `AlgS.Subgroup.*`.
pub(crate) fn declare_category_setoid(
    k: &mut Kernel,
    lg: &LogicPrelude,
    monoid: &RecordNames,
    group: &RecordNames,
    deps: GroupCatDeps,
) -> Result<
    (
        CategoryRecords,
        CategoryNames,
        GroupCatRecords,
        GroupCatNames,
    ),
    KernelError,
> {
    let anon = k.anon();
    let ns = k.name_str(anon, "CatS");
    let recs = declare_category_records(k, lg, ns)?;

    let indiscrete = declare_indiscrete(k, lg, &recs.category, ns)?;
    let of_monoid = declare_of_monoid(k, &recs.category, monoid, ns)?;
    let large_indiscrete = declare_large_indiscrete(k, lg, &recs.category_large, ns)?;
    let grp_indiscrete =
        declare_grp_indiscrete(k, lg, &recs.category_large, large_indiscrete, group, ns)?;
    let id_functor = declare_id_functor(k, &recs.category, &recs.functor, ns)?;
    let of_monoid_hom = declare_of_monoid_hom(k, &recs.functor, monoid, of_monoid, ns)?;

    let is_functor = declare_is_functor(k, lg, &recs.category, ns, "IsFunctor")?;
    let is_nat = declare_is_nat(k, &recs.category, ns)?;
    let is_initial = declare_is_initial(k, &recs.category, ns, false, "IsInitial")?;
    let is_terminal = declare_is_initial(k, &recs.category, ns, true, "IsTerminal")?;
    let is_grp_hom = declare_is_grp_hom(k, lg, group, ns)?;

    let functor_is_functor = declare_functor_is_functor(
        k,
        lg,
        &recs.category,
        &recs.functor,
        is_functor,
        ns,
        "functor_isFunctor",
    )?;
    let is_functor_id = declare_is_functor_id(k, lg, &recs.category, is_functor, ns)?;
    let is_functor_comp = declare_is_functor_comp(k, lg, &recs.category, is_functor, ns)?;
    let is_nat_id = declare_is_nat_id(k, &recs.category, is_nat, ns)?;
    let is_nat_of_monoid = declare_is_nat_of_monoid(k, monoid, of_monoid, is_nat, ns)?;
    let initial_unique = declare_initial_unique(k, lg, &recs.category, is_initial, ns)?;
    let indiscrete_is_initial =
        declare_indiscrete_universal(k, lg, &recs.category, indiscrete, is_initial, ns, false)?;
    let indiscrete_is_terminal =
        declare_indiscrete_universal(k, lg, &recs.category, indiscrete, is_terminal, ns, true)?;
    let is_grp_hom_id = declare_is_grp_hom_id(k, lg, group, is_grp_hom, ns)?;
    let is_grp_hom_comp = declare_is_grp_hom_comp(k, lg, group, is_grp_hom, ns)?;

    let (grp_recs, grp_names) = groups::declare_group_categories(
        k,
        lg,
        &recs,
        monoid,
        group,
        is_grp_hom,
        is_grp_hom_id,
        is_grp_hom_comp,
        deps,
        ns,
    )?;

    Ok((
        recs,
        CategoryNames {
            indiscrete,
            of_monoid,
            large_indiscrete,
            grp_indiscrete,
            id_functor,
            of_monoid_hom,
            is_functor,
            is_nat,
            is_initial,
            is_terminal,
            is_grp_hom,
            functor_is_functor,
            is_functor_id,
            is_functor_comp,
            is_nat_id,
            is_nat_of_monoid,
            initial_unique,
            indiscrete_is_initial,
            indiscrete_is_terminal,
            is_grp_hom_id,
            is_grp_hom_comp,
        },
        grp_recs,
        grp_names,
    ))
}

// ---------------------------------------------------------------------------
// Tests. Every assertion reads the KERNEL.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod category_setoid_tests {
    use super::*;
    use crate::build_logic_prelude;
    use crate::nat_prelude::structures as algeq;
    use crate::nat_prelude::structures_setoid::{
        StructuresSRecordNames, declare_structures_s_all, declare_structures_s_extra,
        intern_structures_s_names,
    };

    struct Fixture {
        lg: LogicPrelude,
        st: StructuresSRecordNames,
        recs: CategoryRecords,
        cs: CategoryNames,
    }

    fn build(k: &mut Kernel) -> Fixture {
        let lg = build_logic_prelude(k).expect("logic prelude must build");
        let alg_p = algeq::intern_structures_names(k);
        let alg_st = algeq::declare_structures_all(k, &alg_p, &lg).expect("Alg spine builds");
        let p = intern_structures_s_names(k);
        let st = declare_structures_s_all(k, &p, &lg).expect("AlgS spine builds");
        let extra = declare_structures_s_extra(k, &lg, &p, &st, &alg_p, &alg_st)
            .expect("the AlgS extras (AlgS.Hom.mapOne) must build");
        let deps = GroupCatDeps {
            map_one: extra.hom_map_one,
        };
        let (recs, cs, _grp_recs, _gs) =
            declare_category_setoid(k, &lg, &st.monoid, &st.group, deps)
                .expect("the setoid-enriched category layer must admit");
        Fixture { lg, st, recs, cs }
    }

    /// A `Sort 1` object type to instantiate the small category at: every
    /// `AlgS` record is `Sort 2`, so the tests use `Prop`, which is `Sort 1`
    /// and is available with only the logic prelude.
    fn sort1_witness(k: &mut Kernel) -> ExprId {
        let l0 = k.level_zero();
        k.sort(l0)
    }

    #[test]
    fn the_category_layer_admits_by_the_setoid_route() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.cs.all() {
            assert!(
                k.environment().get(name).is_some(),
                "declaration missing from the environment"
            );
        }
        for rn in [f.recs.category, f.recs.category_large, f.recs.functor] {
            assert!(k.environment().get(rn.ind).is_some(), "record missing");
            assert!(k.environment().get(rn.mk).is_some(), "constructor missing");
            for i in 0..rn.field_count() {
                assert!(
                    k.environment().get(rn.sel(i)).is_some(),
                    "selector {i} missing"
                );
            }
        }
        assert_eq!(f.recs.category.field_count(), 12);
        assert_eq!(f.recs.category_large.field_count(), 12);
        assert_eq!(f.recs.functor.field_count(), 7);
    }

    /// **The headline claim**, read from `Kernel::axiom_footprint`.
    #[test]
    fn the_category_layer_is_axiom_free() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.cs.all() {
            let footprint = k.axiom_footprint(name);
            assert!(
                footprint.is_empty(),
                "axiom footprint must be empty, got {} entries",
                footprint.len()
            );
        }
        for rn in [f.recs.category, f.recs.category_large, f.recs.functor] {
            for i in 0..rn.field_count() {
                assert!(
                    k.axiom_footprint(rn.sel(i)).is_empty(),
                    "selector footprint must be empty"
                );
            }
        }
    }

    #[test]
    fn the_category_results_are_checked_theorems() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let mut n = 0;
        for name in f.cs.theorems() {
            let d = k.environment().get(name).expect("theorem exists").clone();
            assert!(
                matches!(d, Declaration::Theorem { .. }),
                "must be a checked Theorem"
            );
            n += 1;
        }
        let d = k
            .environment()
            .get(f.cs.is_grp_hom_comp)
            .expect("theorem exists")
            .clone();
        assert!(matches!(d, Declaration::Theorem { .. }));
        n += 1;
        assert_eq!(n, 10, "ten checked theorems");
    }

    /// Prints every rendered type so a referee can read the statements out of
    /// the suite, and pins the two universe levels.
    #[test]
    fn the_category_types_render_and_pin_their_universes() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        for name in f.cs.all() {
            let decl = k.environment().get(name).expect("exists").clone();
            let ty = match &decl {
                Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
                _ => panic!("unexpected declaration kind"),
            };
            let rendered = k.render_lean(ty);
            println!("decl {name:?} :\n  {rendered}\n");
        }
        for rn in [f.recs.category, f.recs.category_large, f.recs.functor] {
            let decl = k.environment().get(rn.ind).expect("exists").clone();
            let Declaration::Inductive { ty, .. } = decl else {
                panic!("record must be an inductive");
            };
            println!("record {:?} : {}", rn.ind, k.render_lean(ty));
        }
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let l2 = k.level_succ(l1);
        let l3 = k.level_succ(l2);
        let sort2 = k.sort(l2);
        let sort3 = k.sort(l3);
        let cat_ty = match k.environment().get(f.recs.category.ind).expect("exists") {
            Declaration::Inductive { ty, .. } => *ty,
            _ => panic!("record must be an inductive"),
        };
        let large_ty = match k
            .environment()
            .get(f.recs.category_large.ind)
            .expect("exists")
        {
            Declaration::Inductive { ty, .. } => *ty,
            _ => panic!("record must be an inductive"),
        };
        assert!(k.def_eq(cat_ty, sort2), "CatS.Category must live at Sort 2");
        assert!(
            !k.def_eq(cat_ty, sort3),
            "CatS.Category must NOT live at Sort 3"
        );
        assert!(
            k.def_eq(large_ty, sort3),
            "CatS.CategoryLarge must live at Sort 3"
        );
        assert!(
            !k.def_eq(large_ty, sort2),
            "CatS.CategoryLarge must NOT live at Sort 2"
        );
    }

    /// **The universe guard, measured verbatim.** The same twelve-field
    /// constructor at `Sort 1` is refused by ADR-1495's
    /// `ConstructorFieldUniverseTooBig` on field 0 (`obj : Sort 1`, which
    /// itself lives at level 2) — and the positive twin at `Sort 2` admits.
    #[test]
    fn the_object_field_forces_the_record_up_a_universe() {
        let mut k = Kernel::new();
        let lg = build_logic_prelude(&mut k).expect("logic prelude");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let l2 = k.level_succ(l1);
        let anon = k.anon();

        let specs = category_fields(FieldKind::CarrierSort);
        let mut ctor_fields: Vec<(u64, ExprId)> = Vec::new();
        let mut vals: Vec<ExprId> = Vec::new();
        for (i, spec) in specs.iter().enumerate() {
            let ty = (spec.build)(&mut k, &lg, l1, &vals);
            let fv = 10_000 + i as u64;
            ctor_fields.push((fv, ty));
            let v = k.fvar(fv);
            vals.push(v);
        }

        let bad = k.name_str(anon, "CatSSort1Control");
        let bad_mk = k.name_str(bad, "mk");
        let bad_const = k.const_(bad, vec![]);
        let bad_ctor = crate::nat_prelude::structures::close_pi(&mut k, &ctor_fields, bad_const);
        let sort1 = k.sort(l1);
        let err = k
            .add_inductive(bad, &[], 0, sort1, &[(bad_mk, bad_ctor)])
            .expect_err("a Sort-1 category record must be REFUSED");
        println!("rejection at Sort 1: {err:?}");
        assert!(
            matches!(
                err,
                KernelError::ConstructorFieldUniverseTooBig { field_index: 0, .. }
            ),
            "expected ConstructorFieldUniverseTooBig on field 0, got {err:?}"
        );

        let good = k.name_str(anon, "CatSSort2Control");
        let good_mk = k.name_str(good, "mk");
        let good_const = k.const_(good, vec![]);
        let good_ctor = crate::nat_prelude::structures::close_pi(&mut k, &ctor_fields, good_const);
        let sort2 = k.sort(l2);
        k.add_inductive(good, &[], 0, sort2, &[(good_mk, good_ctor)])
            .expect("the same field list at Sort 2 must ADMIT");
    }

    /// **Evaluation test for `CatS.indiscrete`.** Every selector reduces to
    /// the hand-written body, and a discriminating negative twin does not.
    #[test]
    fn the_indiscrete_category_reduces_to_its_body() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let a_ty = sort1_witness(&mut k);
        let ind = k.const_(f.cs.indiscrete, vec![]);
        let cv = k.app(ind, a_ty);
        let c = cat_of(&mut k, &f.recs.category, cv);

        assert!(k.def_eq(c.obj, a_ty), "obj must reduce to A");

        let x = k.fvar(90_001);
        let y = k.fvar(90_002);
        let hom_xy = c.hom_ty(&mut k, x, y);
        assert!(k.def_eq(hom_xy, a_ty), "hom x y must reduce to A");

        let g = k.fvar(90_003);
        let h = k.fvar(90_004);
        let eq = c.eqv(&mut k, x, y, g, h);
        let true_c = k.const_(f.lg.true_, vec![]);
        let false_c = k.const_(f.lg.false_, vec![]);
        assert!(k.def_eq(eq, true_c), "homEquiv must reduce to True");
        assert!(!k.def_eq(eq, false_c), "homEquiv must NOT be False");

        let idx_ = c.ident(&mut k, x);
        assert!(k.def_eq(idx_, x), "id x must reduce to x");
        assert!(!k.def_eq(idx_, y), "id x must NOT reduce to y");

        let z = k.fvar(90_005);
        let cmp = c.cmp(&mut k, x, y, z, g, h);
        assert!(k.def_eq(cmp, g), "comp picks the outer morphism");
        assert!(!k.def_eq(cmp, h), "comp must NOT pick the inner morphism");
    }

    /// **Evaluation test for `CatS.ofMonoid`** — the delooping's every field
    /// is the monoid's own, and the composition order is pinned.
    #[test]
    fn the_delooping_reduces_to_the_monoids_own_fields() {
        use algs::monoid::{CARRIER, E, EQUIV, OP};
        let mut k = Kernel::new();
        let f = build(&mut k);
        let a_ty = sort1_witness(&mut k);
        let m = k.fvar(91_000);
        let om = k.const_(f.cs.of_monoid, vec![]);
        let cv = t_app(&mut k, om, &[a_ty, m]);
        let c = cat_of(&mut k, &f.recs.category, cv);

        let carrier = sel(&mut k, &f.st.monoid, CARRIER, m);
        let m_op = sel(&mut k, &f.st.monoid, OP, m);
        let m_e = sel(&mut k, &f.st.monoid, E, m);
        let m_eq = sel(&mut k, &f.st.monoid, EQUIV, m);

        let x = k.fvar(91_001);
        let y = k.fvar(91_002);
        let z = k.fvar(91_003);
        let hom = c.hom_ty(&mut k, x, y);
        assert!(k.def_eq(hom, carrier), "hom must reduce to M.carrier");
        assert!(
            !k.def_eq(hom, a_ty),
            "hom must NOT reduce to the object type"
        );

        let id_x = c.ident(&mut k, x);
        assert!(k.def_eq(id_x, m_e), "id must reduce to M.e");

        let g = k.fvar(91_010);
        let h = k.fvar(91_011);
        let cmp = c.cmp(&mut k, x, y, z, g, h);
        let op_gh = app2(&mut k, m_op, g, h);
        let op_hg = app2(&mut k, m_op, h, g);
        assert!(k.def_eq(cmp, op_gh), "comp g f must reduce to M.op g f");
        assert!(
            !k.def_eq(cmp, op_hg),
            "comp must NOT reduce to the SWAPPED product -- the order is what \
             makes AlgS.Monoid.identL fill idL"
        );

        let eq = c.eqv(&mut k, x, y, g, h);
        let m_eq_gh = app2(&mut k, m_eq, g, h);
        let m_eq_hg = app2(&mut k, m_eq, h, g);
        assert!(k.def_eq(eq, m_eq_gh), "homEquiv must reduce to M.equiv");
        assert!(!k.def_eq(eq, m_eq_hg), "and not to the swapped M.equiv");
    }

    /// **The universe measurement the lane exists to produce**:
    /// `CatS.grpIndiscrete.obj` reduces to `AlgS.Group`, read from the kernel.
    /// Objects of the category of groups are expressible; the hom-family is
    /// what is not.
    #[test]
    fn the_large_category_takes_alg_s_group_as_its_objects() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let gi = k.const_(f.cs.grp_indiscrete, vec![]);
        let obj = sel(&mut k, &f.recs.category_large, OBJ, gi);
        let group_ty = k.const_(f.st.group.ind, vec![]);
        let monoid_ty = k.const_(f.st.monoid.ind, vec![]);
        assert!(
            k.def_eq(obj, group_ty),
            "CatS.grpIndiscrete.obj must reduce to AlgS.Group"
        );
        assert!(
            !k.def_eq(obj, monoid_ty),
            "and must NOT reduce to AlgS.Monoid"
        );
        println!("CatS.grpIndiscrete.obj = {}", k.render_lean(obj));
    }

    /// **Evaluation test for the two functor instances.**
    #[test]
    fn the_functor_instances_reduce_to_their_bodies() {
        use idx::functor::{MAP, OBJ as F_OBJ, SRC, TGT};
        let mut k = Kernel::new();
        let f = build(&mut k);
        let cv = k.fvar(92_000);

        let idf = k.const_(f.cs.id_functor, vec![]);
        let fv = k.app(idf, cv);
        let src = sel(&mut k, &f.recs.functor, SRC, fv);
        let tgt = sel(&mut k, &f.recs.functor, TGT, fv);
        assert!(k.def_eq(src, cv), "idFunctor.src == C");
        assert!(k.def_eq(tgt, cv), "idFunctor.tgt == C");
        let c = cat_of(&mut k, &f.recs.category, cv);
        let fo = sel(&mut k, &f.recs.functor, F_OBJ, fv);
        let a = k.fvar(92_001);
        let b = k.fvar(92_002);
        let fo_a = k.app(fo, a);
        assert!(k.def_eq(fo_a, a), "idFunctor.obj a == a");
        assert!(!k.def_eq(fo_a, b), "and NOT b");
        let fm = sel(&mut k, &f.recs.functor, MAP, fv);
        let mor = k.fvar(92_003);
        let fm_x = t_app(&mut k, fm, &[a, b, mor]);
        assert!(k.def_eq(fm_x, mor), "idFunctor.map a b f == f");
        let id_a = c.ident(&mut k, a);
        assert!(!k.def_eq(fm_x, id_a), "and NOT the identity morphism");

        let a_ty = sort1_witness(&mut k);
        let m = k.fvar(92_010);
        let n = k.fvar(92_011);
        let hfn = k.fvar(92_012);
        let hc = k.fvar(92_013);
        let hop = k.fvar(92_014);
        let he = k.fvar(92_015);
        let omh = k.const_(f.cs.of_monoid_hom, vec![]);
        let fv2 = t_app(&mut k, omh, &[a_ty, m, n, hfn, hc, hop, he]);
        let fm2 = sel(&mut k, &f.recs.functor, MAP, fv2);
        let x = k.fvar(92_020);
        let y = k.fvar(92_021);
        let mor2 = k.fvar(92_022);
        let applied = t_app(&mut k, fm2, &[x, y, mor2]);
        let expected = k.app(hfn, mor2);
        assert!(k.def_eq(applied, expected), "ofMonoidHom.map a b f == h f");
        assert!(
            !k.def_eq(applied, mor2),
            "and NOT f -- the functor must actually apply h"
        );
    }

    /// **Evaluation test for `CatS.IsInitial`** — it unfolds to the pointwise
    /// uniqueness statement, and NOT to the terminal one.
    #[test]
    fn is_initial_unfolds_to_pointwise_uniqueness() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let cv = k.fvar(93_000);
        let c = cat_of(&mut k, &f.recs.category, cv);
        let a = k.fvar(93_001);
        let med = k.fvar(93_002);

        let isi = k.const_(f.cs.is_initial, vec![]);
        let lhs = t_app(&mut k, isi, &[cv, a, med]);

        let b = k.fvar(93_010);
        let hom = c.hom_ty(&mut k, a, b);
        let g = k.fvar(93_011);
        let medb = k.app(med, b);
        let body = c.eqv(&mut k, a, b, medb, g);
        let rhs = pi_over(&mut k, 93_011, hom, body);
        let rhs = pi_over(&mut k, 93_010, c.obj, rhs);
        assert!(
            k.def_eq(lhs, rhs),
            "IsInitial must unfold to forall b g, homEquiv a b (med b) g"
        );

        let ist = k.const_(f.cs.is_terminal, vec![]);
        let dual = t_app(&mut k, ist, &[cv, a, med]);
        assert!(
            !k.def_eq(lhs, dual),
            "IsInitial and IsTerminal must be different propositions"
        );
    }

    // -----------------------------------------------------------------------
    // Mutation table. Each entry states a MUTATED type and offers the
    // UNMUTATED proof term; the kernel must refuse. Every mutation is paired
    // with the unmutated positive twin IN THE SAME TEST, so a test that has
    // stopped exercising the kernel fails on the twin.
    // -----------------------------------------------------------------------

    /// M1. A "functor" whose morphism map is a CONSTANT does not preserve
    /// identities, and the identity functor's proof is refused for it.
    #[test]
    fn m1_a_constant_morphism_map_is_not_a_functor() {
        use algs::monoid::CARRIER;
        let mut k = Kernel::new();
        let f = build(&mut k);
        let anon = k.anon();
        let a_ty = sort1_witness(&mut k);
        let m = k.fvar(94_000);
        let mon_ty = k.const_(f.st.monoid.ind, vec![]);
        let om = k.const_(f.cs.of_monoid, vec![]);
        let cv = t_app(&mut k, om, &[a_ty, m]);
        let c = cat_of(&mut k, &f.recs.category, cv);
        let carrier = sel(&mut k, &f.st.monoid, CARRIER, m);
        let nelt = k.fvar(94_001);

        let fo = {
            let a = k.fvar(94_010);
            lam_over(&mut k, 94_010, c.obj, a)
        };
        let good_fm = {
            let a = k.fvar(94_010);
            let b = k.fvar(94_011);
            let hab = c.hom_ty(&mut k, a, b);
            let mor = k.fvar(94_012);
            let t = lam_over(&mut k, 94_012, hab, mor);
            let t = lam_over(&mut k, 94_011, c.obj, t);
            lam_over(&mut k, 94_010, c.obj, t)
        };
        // THE MUTATION: `fun a b f => n` instead of `fun a b f => f`.
        let bad_fm = {
            let a = k.fvar(94_010);
            let b = k.fvar(94_011);
            let hab = c.hom_ty(&mut k, a, b);
            let t = lam_over(&mut k, 94_012, hab, nelt);
            let t = lam_over(&mut k, 94_011, c.obj, t);
            lam_over(&mut k, 94_010, c.obj, t)
        };

        let isf = k.const_(f.cs.is_functor, vec![]);
        let good_stmt = t_app(&mut k, isf, &[cv, cv, fo, good_fm]);
        let isf2 = k.const_(f.cs.is_functor, vec![]);
        let bad_stmt = t_app(&mut k, isf2, &[cv, cv, fo, bad_fm]);

        let idf = k.const_(f.cs.is_functor_id, vec![]);
        let applied = k.app(idf, cv);
        let proof = {
            let t = lam_over(&mut k, 94_001, carrier, applied);
            lam_over(&mut k, 94_000, mon_ty, t)
        };

        let good_ty = {
            let t = pi_over(&mut k, 94_001, carrier, good_stmt);
            pi_over(&mut k, 94_000, mon_ty, t)
        };
        let good_name = k.name_str(anon, "m1Positive");
        k.add_declaration(Declaration::Theorem {
            name: good_name,
            uparams: vec![],
            ty: good_ty,
            value: proof,
        })
        .expect("the identity functor IS a functor");

        let bad_ty = {
            let t = pi_over(&mut k, 94_001, carrier, bad_stmt);
            pi_over(&mut k, 94_000, mon_ty, t)
        };
        let bad_name = k.name_str(anon, "m1Mutant");
        let err = k
            .add_declaration(Declaration::Theorem {
                name: bad_name,
                uparams: vec![],
                ty: bad_ty,
                value: proof,
            })
            .expect_err("a constant morphism map must NOT be admitted as a functor");
        println!("M1 rejection: {err:?}");
    }

    /// M2. The initial-object isomorphism with one composite built from the
    /// WRONG mediating map is refused.
    #[test]
    fn m2_the_isomorphism_needs_both_mediating_maps() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let anon = k.anon();
        let cv = k.fvar(95_000);
        let cat_ty = k.const_(f.recs.category.ind, vec![]);
        let c = cat_of(&mut k, &f.recs.category, cv);
        let a = k.fvar(95_001);
        let b = k.fvar(95_002);
        let med_a_t = med_out_ty(&mut k, &c, a);
        let med_b_t = med_out_ty(&mut k, &c, b);
        let med_a = k.fvar(95_003);
        let med_b = k.fvar(95_004);
        let isi = k.const_(f.cs.is_initial, vec![]);
        let ha_ty = t_app(&mut k, isi, &[cv, a, med_a]);
        let isi2 = k.const_(f.cs.is_initial, vec![]);
        let hb_ty = t_app(&mut k, isi2, &[cv, b, med_b]);
        let ha = k.fvar(95_005);

        let med_a_b = k.app(med_a, b);
        let med_b_a = k.app(med_b, a);
        let med_a_a = k.app(med_a, a);
        let good_round = c.cmp(&mut k, a, b, a, med_b_a, med_a_b);
        let id_a = c.ident(&mut k, a);
        let good_p = c.eqv(&mut k, a, a, good_round, id_a);

        let u1 = t_app(&mut k, ha, &[a, good_round]);
        let v1 = c.sy(&mut k, a, a, med_a_a, good_round, u1);
        let w1 = t_app(&mut k, ha, &[a, id_a]);
        let pf = c.tr(&mut k, a, a, good_round, med_a_a, id_a, v1, w1);

        let close_ty = |k: &mut Kernel, e: ExprId| -> ExprId {
            let t = pi_over(k, 95_006, hb_ty, e);
            let t = pi_over(k, 95_005, ha_ty, t);
            let t = pi_over(k, 95_004, med_b_t, t);
            let t = pi_over(k, 95_002, c.obj, t);
            let t = pi_over(k, 95_003, med_a_t, t);
            let t = pi_over(k, 95_001, c.obj, t);
            pi_over(k, 95_000, cat_ty, t)
        };
        let close_val = |k: &mut Kernel, e: ExprId| -> ExprId {
            let t = lam_over(k, 95_006, hb_ty, e);
            let t = lam_over(k, 95_005, ha_ty, t);
            let t = lam_over(k, 95_004, med_b_t, t);
            let t = lam_over(k, 95_002, c.obj, t);
            let t = lam_over(k, 95_003, med_a_t, t);
            let t = lam_over(k, 95_001, c.obj, t);
            lam_over(k, 95_000, cat_ty, t)
        };

        let good_ty = close_ty(&mut k, good_p);
        let good_val = close_val(&mut k, pf);
        let good_name = k.name_str(anon, "m2Positive");
        k.add_declaration(Declaration::Theorem {
            name: good_name,
            uparams: vec![],
            ty: good_ty,
            value: good_val,
        })
        .expect("the round trip through both mediating maps IS the identity");

        // THE MUTATION: the round trip built from `medA b` twice.
        let bad_round = c.cmp(&mut k, a, b, a, med_a_b, med_a_b);
        let bad_p = c.eqv(&mut k, a, a, bad_round, id_a);
        let bad_ty = close_ty(&mut k, bad_p);
        let bad_val = close_val(&mut k, pf);
        let bad_name = k.name_str(anon, "m2Mutant");
        let err = k
            .add_declaration(Declaration::Theorem {
                name: bad_name,
                uparams: vec![],
                ty: bad_ty,
                value: bad_val,
            })
            .expect_err("the wrong composite must NOT be admitted");
        println!("M2 rejection: {err:?}");
    }

    /// M3. The naturality square with the wrong right-hand side is refused.
    #[test]
    fn m3_the_naturality_square_is_indexed() {
        let mut k = Kernel::new();
        let f = build(&mut k);
        let anon = k.anon();
        let cv = k.fvar(96_000);
        let cat_ty = k.const_(f.recs.category.ind, vec![]);
        let c = cat_of(&mut k, &f.recs.category, cv);

        let a = k.fvar(96_001);
        let b = k.fvar(96_002);
        let hab = c.hom_ty(&mut k, a, b);
        let mor = k.fvar(96_003);
        let ib = c.ident(&mut k, b);
        let ia = c.ident(&mut k, a);
        let lhs = c.cmp(&mut k, a, b, b, ib, mor);
        let rhs = c.cmp(&mut k, a, a, b, mor, ia);
        let good_stmt = c.eqv(&mut k, a, b, lhs, rhs);

        let idl = sel(&mut k, &f.recs.category, ID_L, cv);
        let h1 = t_app(&mut k, idl, &[a, b, mor]);
        let idr = sel(&mut k, &f.recs.category, ID_R, cv);
        let h2raw = t_app(&mut k, idr, &[a, b, mor]);
        let h2 = c.sy(&mut k, a, b, rhs, mor, h2raw);
        let pf = c.tr(&mut k, a, b, lhs, mor, rhs, h1, h2);

        let close_ty = |k: &mut Kernel, e: ExprId| -> ExprId {
            let t = pi_over(k, 96_003, hab, e);
            let t = pi_over(k, 96_002, c.obj, t);
            let t = pi_over(k, 96_001, c.obj, t);
            pi_over(k, 96_000, cat_ty, t)
        };
        let close_val = |k: &mut Kernel, e: ExprId| -> ExprId {
            let t = lam_over(k, 96_003, hab, e);
            let t = lam_over(k, 96_002, c.obj, t);
            let t = lam_over(k, 96_001, c.obj, t);
            lam_over(k, 96_000, cat_ty, t)
        };

        let good_name = k.name_str(anon, "m3Positive");
        let good_ty = close_ty(&mut k, good_stmt);
        let good_val = close_val(&mut k, pf);
        k.add_declaration(Declaration::Theorem {
            name: good_name,
            uparams: vec![],
            ty: good_ty,
            value: good_val,
        })
        .expect("the identity natural transformation's square holds");

        // THE MUTATION: the right-hand side is `id b`, not `f . id a`.
        let bad_stmt = c.eqv(&mut k, a, b, lhs, ib);
        let bad_ty = close_ty(&mut k, bad_stmt);
        let bad_val = close_val(&mut k, pf);
        let bad_name = k.name_str(anon, "m3Mutant");
        let err = k
            .add_declaration(Declaration::Theorem {
                name: bad_name,
                uparams: vec![],
                ty: bad_ty,
                value: bad_val,
            })
            .expect_err("a square with the wrong right-hand side must NOT be admitted");
        println!("M3 rejection: {err:?}");
    }

    /// M4. `isGrpHom_comp` with the composite in the WRONG order is refused.
    #[test]
    fn m4_the_composite_group_hom_is_ordered() {
        use algs::group::CARRIER;
        let mut k = Kernel::new();
        let f = build(&mut k);
        let anon = k.anon();
        let g_ty = k.const_(f.st.group.ind, vec![]);
        let g = k.fvar(97_000);
        let h = k.fvar(97_001);
        let gc = sel(&mut k, &f.st.group, CARRIER, g);
        let hc = sel(&mut k, &f.st.group, CARRIER, h);
        let f1 = k.fvar(97_002);
        let f2 = k.fvar(97_003);
        let f1_ty = arrow(&mut k, gc, hc);
        let f2_ty = arrow(&mut k, hc, gc);

        let igh = k.const_(f.cs.is_grp_hom, vec![]);
        let h1_ty = t_app(&mut k, igh, &[g, h, f1]);
        let igh2 = k.const_(f.cs.is_grp_hom, vec![]);
        let h2_ty = t_app(&mut k, igh2, &[h, g, f2]);
        let hh1 = k.fvar(97_004);
        let hh2 = k.fvar(97_005);

        let good_comp = {
            let x = k.fvar(97_010);
            let inner = k.app(f1, x);
            let body = k.app(f2, inner);
            lam_over(&mut k, 97_010, gc, body)
        };
        let ighc = k.const_(f.cs.is_grp_hom_comp, vec![]);
        let pf = t_app(&mut k, ighc, &[g, h, g, f1, f2, hh1, hh2]);
        let igh3 = k.const_(f.cs.is_grp_hom, vec![]);
        let good_stmt = t_app(&mut k, igh3, &[g, g, good_comp]);

        let close_ty = |k: &mut Kernel, e: ExprId| -> ExprId {
            let t = pi_over(k, 97_005, h2_ty, e);
            let t = pi_over(k, 97_004, h1_ty, t);
            let t = pi_over(k, 97_003, f2_ty, t);
            let t = pi_over(k, 97_002, f1_ty, t);
            let t = pi_over(k, 97_001, g_ty, t);
            pi_over(k, 97_000, g_ty, t)
        };
        let close_val = |k: &mut Kernel, e: ExprId| -> ExprId {
            let t = lam_over(k, 97_005, h2_ty, e);
            let t = lam_over(k, 97_004, h1_ty, t);
            let t = lam_over(k, 97_003, f2_ty, t);
            let t = lam_over(k, 97_002, f1_ty, t);
            let t = lam_over(k, 97_001, g_ty, t);
            lam_over(k, 97_000, g_ty, t)
        };

        let good_name = k.name_str(anon, "m4Positive");
        let good_ty = close_ty(&mut k, good_stmt);
        let good_val = close_val(&mut k, pf);
        k.add_declaration(Declaration::Theorem {
            name: good_name,
            uparams: vec![],
            ty: good_ty,
            value: good_val,
        })
        .expect("f2 . f1 IS a homomorphism when both are");

        // THE MUTATION: the conclusion names `f1 . f1`, not `f2 . f1`.
        let bad_comp = {
            let x = k.fvar(97_010);
            let inner = k.app(f1, x);
            let body = k.app(f1, inner);
            lam_over(&mut k, 97_010, gc, body)
        };
        let igh4 = k.const_(f.cs.is_grp_hom, vec![]);
        let bad_stmt = t_app(&mut k, igh4, &[g, g, bad_comp]);
        let bad_ty = close_ty(&mut k, bad_stmt);
        let bad_val = close_val(&mut k, pf);
        let bad_name = k.name_str(anon, "m4Mutant");
        let err = k
            .add_declaration(Declaration::Theorem {
                name: bad_name,
                uparams: vec![],
                ty: bad_ty,
                value: bad_val,
            })
            .expect_err("the wrong composite must NOT be admitted");
        println!("M4 rejection: {err:?}");
    }
}
