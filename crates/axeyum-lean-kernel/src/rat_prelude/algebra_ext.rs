//! ADR-1584 (amending ADR-1578): forgetful projections between the `Alg.*`
//! records, cross-carrier generic theorems that retire (or would retire)
//! hand-proved carrier-specific lemmas, and `Alg.OrderedRing`.
//!
//! ADR-1578's spine is deliberately flat — no inheritance, no coercion — so
//! `Alg.monoidIdentUnique (CommMonoid.toMonoid M)` type-checks only once a
//! genuine forgetful projection exists; applying a `Monoid` theorem directly
//! to a `CommMonoid`/`Group`/... instance is a `TypeMismatch`, measured in
//! ADR-1578 itself. Every projection here is a `Definition`
//! `<Record>.mk` applied to the source record's own selectors (plus, for
//! `Ring.toCommGroup`, two DERIVED law fields the target record needs but
//! the source does not carry as a primitive — the same
//! [`derive_left_unit`]/`derive_inv_left` shape ADR-1578's own instance
//! builders already use for `Rat`'s missing `one_mul` and `Int`'s missing
//! `zero_add`).
//!
//! Every generic theorem below is proved ONCE over the record and
//! instantiated at ℕ/ℤ/ℚ (or ℤ/ℚ, where the theorem needs a genuine
//! two-sided inverse and ℕ's multiplicative monoid has none). See
//! `retirement_tests` for which hand-proved carrier-specific lemma each one
//! could retire, and which cannot be retired because the instance site's own
//! proof cites the very lemma being replaced (ADR-1581's rule, general here:
//! "a hand proof's citations are necessary, not sufficient").

use super::RatPrelude;
use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::nat_prelude::structures::{
    self, RecordNames, app2, arrow, congr_arg, derive_left_unit, eq_of, lam_over, mk_instance,
    pi_over, sel, subst, symm_of, trans_of,
};

// ---------------------------------------------------------------------------
// Small helpers.
// ---------------------------------------------------------------------------

/// `∀ a, add (neg a) a = zero`, derived from `add_comm` + `neg_add : ∀a, add
/// a (neg a) = zero` — the same shape as `derive_left_unit`, but for the
/// two-sided-inverse law rather than a unit law (no `unit`/identity
/// argument: the "right" fact being mirrored is `neg_add` itself, applied at
/// `a`, not a caller-supplied constant).
#[allow(clippy::too_many_arguments)]
fn derive_inv_left(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    carrier_ty: ExprId,
    zero: ExprId,
    add: ExprId,
    neg: ExprId,
    add_comm: ExprId,
    neg_add_right: ExprId,
    a_fv: u64,
    scratch_fv: u64,
) -> ExprId {
    let a = k.fvar(a_fv);
    let na = k.app(neg, a);
    let add_na_a = app2(k, add, na, a);
    let add_a_na = app2(k, add, a, na);
    let comm_na_a = {
        let e1 = k.app(add_comm, na);
        k.app(e1, a)
    }; // : add (neg a) a = add a (neg a)
    let negadd_a = k.app(neg_add_right, a); // : add a (neg a) = zero
    let body = trans_of(
        k, lg, l1, carrier_ty, add_na_a, add_a_na, zero, comm_na_a, negadd_a, scratch_fv,
    );
    lam_over(k, a_fv, carrier_ty, body)
}

// ---------------------------------------------------------------------------
// Forgetful projections (deliverable 2).
// ---------------------------------------------------------------------------

/// A `<Record>.mk` applied to the source's OWN selectors (in the target
/// record's field order) — one `Definition`, `src -> dst`.
fn declare_projection(
    k: &mut Kernel,
    name: NameId,
    src: &RecordNames,
    dst: &RecordNames,
    s_fv: u64,
    build_args: &dyn Fn(&mut Kernel, ExprId) -> Vec<ExprId>,
) -> Result<(), KernelError> {
    let src_ty = k.const_(src.ind, vec![]);
    let dst_ty = k.const_(dst.ind, vec![]);
    let s = k.fvar(s_fv);
    let args = build_args(k, s);
    let value = mk_instance(k, dst, &args);
    let value = lam_over(k, s_fv, src_ty, value);
    let ty = arrow(k, src_ty, dst_ty);
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// A projection whose target record's fields are literally a PREFIX of the
/// source's own field list, in the same order (`CommMonoid->Monoid`,
/// `CommGroup->Group`, `CommRing->Ring`, `Field->CommRing`): field `i` of
/// `dst` is field `i` of `src`, for every `i < dst.field_count()`.
fn declare_prefix_projection(
    k: &mut Kernel,
    name: NameId,
    src: &RecordNames,
    dst: &RecordNames,
    s_fv: u64,
) -> Result<(), KernelError> {
    let n = dst.field_count();
    declare_projection(k, name, src, dst, s_fv, &move |k2, s| {
        (0..n).map(|i| sel(k2, src, i, s)).collect()
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn declare_projections_all(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures::StructuresNames,
    names: &AlgebraExtNames,
) -> Result<(), KernelError> {
    const S_FV: u64 = 22_000;

    // CommMonoid.toMonoid : the first 6 fields of CommMonoid ARE Monoid's 6
    // fields, in the same order (`comm_monoid_fields()` = `monoid_fields()` +
    // `comm`).
    declare_prefix_projection(
        k,
        names.comm_monoid_to_monoid,
        &st.comm_monoid,
        &st.monoid,
        S_FV,
    )?;

    // Group.toMonoid : Monoid's 6 fields are Group's fields at indices
    // 0,1,2,4,5,6 (Group's INV=3 is dropped).
    {
        use structures::idx::group::{ASSOC, CARRIER, E, IDENT_L, IDENT_R, OP};
        let ty = k.const_(st.group.ind, vec![]);
        let dst_ty = k.const_(st.monoid.ind, vec![]);
        let s = k.fvar(S_FV);
        let args = vec![
            sel(k, &st.group, CARRIER, s),
            sel(k, &st.group, OP, s),
            sel(k, &st.group, E, s),
            sel(k, &st.group, ASSOC, s),
            sel(k, &st.group, IDENT_L, s),
            sel(k, &st.group, IDENT_R, s),
        ];
        let value = mk_instance(k, &st.monoid, &args);
        let value = lam_over(k, S_FV, ty, value);
        let fty = arrow(k, ty, dst_ty);
        k.add_declaration(Declaration::Definition {
            name: names.group_to_monoid,
            uparams: vec![],
            ty: fty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // CommGroup.toGroup : the first 9 fields of CommGroup ARE Group's 9
    // fields, in the same order.
    declare_prefix_projection(
        k,
        names.comm_group_to_group,
        &st.comm_group,
        &st.group,
        S_FV,
    )?;

    // Ring.toMonoid (MULTIPLICATIVE): Monoid's 6 fields are Ring's
    // carrier/mul/one/mulAssoc/mulOneL/mulOneR — every one a direct selector,
    // no derivation.
    {
        use structures::idx::ring::{CARRIER, MUL, MUL_ASSOC, MUL_ONE_L, MUL_ONE_R, ONE};
        let ty = k.const_(st.ring.ind, vec![]);
        let dst_ty = k.const_(st.monoid.ind, vec![]);
        let s = k.fvar(S_FV);
        let args = vec![
            sel(k, &st.ring, CARRIER, s),
            sel(k, &st.ring, MUL, s),
            sel(k, &st.ring, ONE, s),
            sel(k, &st.ring, MUL_ASSOC, s),
            sel(k, &st.ring, MUL_ONE_L, s),
            sel(k, &st.ring, MUL_ONE_R, s),
        ];
        let value = mk_instance(k, &st.monoid, &args);
        let value = lam_over(k, S_FV, ty, value);
        let fty = arrow(k, ty, dst_ty);
        k.add_declaration(Declaration::Definition {
            name: names.ring_to_monoid,
            uparams: vec![],
            ty: fty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // Ring.toCommGroup (ADDITIVE): CommGroup's 10 fields from Ring's additive
    // structure. `identL`/`invL` have no Ring primitive and are DERIVED from
    // `addComm` + `addZero`/`negAdd`.
    {
        use structures::idx::ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, NEG, NEG_ADD, ZERO,
        };
        const A_FV: u64 = 22_001;
        const SC_FV: u64 = 22_002;
        const B_FV: u64 = 22_003;
        const SC2_FV: u64 = 22_004;
        let ty = k.const_(st.ring.ind, vec![]);
        let dst_ty = k.const_(st.comm_group.ind, vec![]);
        let s = k.fvar(S_FV);
        let carrier = sel(k, &st.ring, CARRIER, s);
        let zero = sel(k, &st.ring, ZERO, s);
        let add = sel(k, &st.ring, ADD, s);
        let neg = sel(k, &st.ring, NEG, s);
        let add_assoc = sel(k, &st.ring, ADD_ASSOC, s);
        let add_comm = sel(k, &st.ring, ADD_COMM, s);
        let add_zero = sel(k, &st.ring, ADD_ZERO, s);
        let neg_add = sel(k, &st.ring, NEG_ADD, s);
        let ident_l = derive_left_unit(
            k, lg, l1, carrier, add, zero, add_comm, add_zero, A_FV, SC_FV,
        );
        let inv_l = derive_inv_left(
            k, lg, l1, carrier, zero, add, neg, add_comm, neg_add, B_FV, SC2_FV,
        );
        let args = vec![
            carrier, add, zero, neg, add_assoc, ident_l, add_zero, inv_l, neg_add, add_comm,
        ];
        let value = mk_instance(k, &st.comm_group, &args);
        let value = lam_over(k, S_FV, ty, value);
        let fty = arrow(k, ty, dst_ty);
        k.add_declaration(Declaration::Definition {
            name: names.ring_to_comm_group,
            uparams: vec![],
            ty: fty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // CommRing.toRing : the first 15 fields of CommRing ARE Ring's 15
    // fields, in the same order.
    declare_prefix_projection(k, names.comm_ring_to_ring, &st.comm_ring, &st.ring, S_FV)?;

    // Field.toCommRing : the first 16 fields of Field ARE CommRing's 16
    // fields, in the same order.
    declare_prefix_projection(k, names.field_to_comm_ring, &st.field, &st.comm_ring, S_FV)?;

    Ok(())
}

// ---------------------------------------------------------------------------
// `Alg.OrderedRing` instances (deliverable 5).
// ---------------------------------------------------------------------------

fn declare_ordered_ring_instances(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    p: &RatPrelude,
    st: &structures::StructuresNames,
    names: &AlgebraExtNames,
) -> Result<(), KernelError> {
    use structures::idx::ordered_ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_LE_ADD_LEFT, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, LE,
        LE_ANTISYMM, LE_REFL, LE_TRANS, MUL, MUL_ASSOC, MUL_NONNEG, MUL_ONE_L, MUL_ONE_R, NEG,
        NEG_ADD, ONE, ZERO,
    };
    let ip = p.int;
    let np = p.int.nat;

    // --- Int.orderedRing ----------------------------------------------------
    {
        let int_ty = k.const_(ip.z, vec![]);
        let zero = k.const_(ip.zero, vec![]);
        let one = k.const_(ip.one, vec![]);
        let add = k.const_(ip.add, vec![]);
        let mul = k.const_(ip.mul, vec![]);
        let add_assoc = k.const_(ip.add_assoc, vec![]);
        let add_comm = k.const_(ip.add_comm, vec![]);
        let add_zero = k.const_(ip.add_zero, vec![]);
        let mul_assoc = k.const_(ip.mul_assoc, vec![]);
        let mul_one_l = k.const_(ip.one_mul, vec![]);
        let mul_one_r = k.const_(ip.mul_one, vec![]);
        let distrib_l = k.const_(ip.left_distrib, vec![]);
        let distrib_r = k.const_(ip.add_mul, vec![]);
        let neg = k.const_(ip.neg, vec![]);
        let neg_add = k.const_(ip.add_neg, vec![]);
        let le = k.const_(ip.le, vec![]);
        let le_refl = k.const_(ip.le_refl, vec![]);
        let le_trans = k.const_(ip.le_trans, vec![]);
        let le_antisymm = k.const_(ip.le_antisymm, vec![]);
        let add_le_add_left = k.const_(ip.add_le_add_left, vec![]);
        let mul_nonneg = k.const_(ip.mul_nonneg, vec![]);
        let mut args = vec![ExprId(0); MUL_NONNEG + 1];
        args[CARRIER] = int_ty;
        args[ZERO] = zero;
        args[ONE] = one;
        args[ADD] = add;
        args[MUL] = mul;
        args[ADD_ASSOC] = add_assoc;
        args[ADD_COMM] = add_comm;
        args[ADD_ZERO] = add_zero;
        args[MUL_ASSOC] = mul_assoc;
        args[MUL_ONE_L] = mul_one_l;
        args[MUL_ONE_R] = mul_one_r;
        args[DISTRIB_L] = distrib_l;
        args[DISTRIB_R] = distrib_r;
        args[NEG] = neg;
        args[NEG_ADD] = neg_add;
        args[LE] = le;
        args[LE_REFL] = le_refl;
        args[LE_TRANS] = le_trans;
        args[LE_ANTISYMM] = le_antisymm;
        args[ADD_LE_ADD_LEFT] = add_le_add_left;
        args[MUL_NONNEG] = mul_nonneg;
        let ty = k.const_(st.ordered_ring.ind, vec![]);
        let value = mk_instance(k, &st.ordered_ring, &args);
        k.add_declaration(Declaration::Definition {
            name: names.int_ordered_ring,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // --- Rat.orderedRing ------------------------------------------------------
    // `add_le_add_left` has no `Rat` primitive; derived from `add_le_add` +
    // `le_refl` (`add_le_add(c,c,a,b,le_refl c,hab) : le (c+a) (c+b)`).
    {
        const C_FV: u64 = 22_012;
        const A_FV: u64 = 22_013;
        const B_FV: u64 = 22_014;
        const H_FV: u64 = 22_015;
        let rat_ty = k.const_(p.int.rat, vec![]);
        let zero = k.const_(p.zero, vec![]);
        let one = k.const_(p.one, vec![]);
        let add = k.const_(p.int.rat_add, vec![]);
        let mul = k.const_(p.int.rat_mul, vec![]);
        let add_assoc = k.const_(p.add_assoc, vec![]);
        let add_comm = k.const_(p.add_comm, vec![]);
        let add_zero = k.const_(p.add_zero, vec![]);
        let mul_assoc = k.const_(p.mul_assoc, vec![]);
        let mul_comm = k.const_(p.mul_comm, vec![]);
        let mul_one_r = k.const_(p.mul_one, vec![]);
        let mul_one_l = derive_left_unit(
            k, lg, l1, rat_ty, mul, one, mul_comm, mul_one_r, 22_010, 22_011,
        );
        let distrib_l = k.const_(p.left_distrib, vec![]);
        let distrib_r = k.const_(p.right_distrib, vec![]);
        let neg = k.const_(p.int.rat_neg, vec![]);
        let neg_add = k.const_(p.add_neg, vec![]);
        let le = k.const_(p.le, vec![]);
        let le_refl = k.const_(p.le_refl, vec![]);
        let le_trans = k.const_(p.le_trans, vec![]);
        let le_antisymm = k.const_(p.le_antisymm, vec![]);
        let mul_nonneg = k.const_(p.mul_nonneg, vec![]);

        let add_le_add_left = {
            let add_le_add = k.const_(p.add_le_add, vec![]);
            let c = k.fvar(C_FV);
            let a = k.fvar(A_FV);
            let b = k.fvar(B_FV);
            let le_refl_c = k.app(le_refl, c);
            let h = k.fvar(H_FV);
            let applied = {
                let e1 = k.app(add_le_add, c);
                let e2 = k.app(e1, c);
                let e3 = k.app(e2, a);
                let e4 = k.app(e3, b);
                let e5 = k.app(e4, le_refl_c);
                k.app(e5, h)
            };
            // Field order is `forall a b c, le a b -> le (add c a) (add c
            // b)` -- `a` outermost, `h` innermost -- so bind in that order
            // (innermost first).
            let hab = app2(k, le, a, b);
            let value = lam_over(k, H_FV, hab, applied);
            let value = lam_over(k, C_FV, rat_ty, value);
            let value = lam_over(k, B_FV, rat_ty, value);
            lam_over(k, A_FV, rat_ty, value)
        };

        let mut args = vec![ExprId(0); MUL_NONNEG + 1];
        args[CARRIER] = rat_ty;
        args[ZERO] = zero;
        args[ONE] = one;
        args[ADD] = add;
        args[MUL] = mul;
        args[ADD_ASSOC] = add_assoc;
        args[ADD_COMM] = add_comm;
        args[ADD_ZERO] = add_zero;
        args[MUL_ASSOC] = mul_assoc;
        args[MUL_ONE_L] = mul_one_l;
        args[MUL_ONE_R] = mul_one_r;
        args[DISTRIB_L] = distrib_l;
        args[DISTRIB_R] = distrib_r;
        args[NEG] = neg;
        args[NEG_ADD] = neg_add;
        args[LE] = le;
        args[LE_REFL] = le_refl;
        args[LE_TRANS] = le_trans;
        args[LE_ANTISYMM] = le_antisymm;
        args[ADD_LE_ADD_LEFT] = add_le_add_left;
        args[MUL_NONNEG] = mul_nonneg;
        let ty = k.const_(st.ordered_ring.ind, vec![]);
        let value = mk_instance(k, &st.ordered_ring, &args);
        k.add_declaration(Declaration::Definition {
            name: names.rat_ordered_ring,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    let _ = np;
    Ok(())
}

// ---------------------------------------------------------------------------
// Generic theorems (deliverable 3).
// ---------------------------------------------------------------------------
//
// `Alg.mul_left_cancel` moved to `nat_prelude::structures` (ADR-1587 §1) --
// see `declare_mul_left_cancel_early` there and its call site in
// `nat_prelude::build_nat_prelude_uncached`, right after the structures
// spine itself. `declare_algebra_ext_all` below no longer declares it.

/// `Alg.neg_neg : forall (G:Group)(a:G.carrier), G.inv(G.inv a)=a`. A direct
/// instantiation of `Alg.groupInvUnique` at `(x := G.inv a, b := G.inv(G.inv
/// a), c := a)`, `h1 := invL(G.inv a)`, `h2 := invL a` — no new proof
/// engineering.
fn build_neg_neg(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
    group_inv_unique: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::group::{CARRIER, INV, INV_L};
    const G_FV: u64 = 22_150;
    const A_FV: u64 = 22_151;

    let ind_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(G_FV);
    let carrier = sel(k, group, CARRIER, g);
    let inv = sel(k, group, INV, g);
    let inv_l = sel(k, group, INV_L, g);
    let a = k.fvar(A_FV);
    let inv_a = k.app(inv, a);
    let inv_inv_a = k.app(inv, inv_a);

    let thm = k.const_(group_inv_unique, vec![]);
    let h1 = k.app(inv_l, inv_a); // : op (inv (inv a)) (inv a) = e
    let h2 = k.app(inv_l, a); // : op (inv a) a = e
    let applied = {
        let e1 = k.app(thm, g);
        let e2 = k.app(e1, inv_a);
        let e3 = k.app(e2, inv_inv_a);
        let e4 = k.app(e3, a);
        let e5 = k.app(e4, h1);
        k.app(e5, h2)
    };

    let value = lam_over(k, A_FV, carrier, applied);
    let value = lam_over(k, G_FV, ind_ty, value);

    let concl = eq_of(k, lg, l1, carrier, inv_inv_a, a);
    let ty = pi_over(k, A_FV, carrier, concl);
    let ty = pi_over(k, G_FV, ind_ty, ty);

    (ty, value)
}

/// `Alg.sub : Pi (R:Ring), R.carrier -> R.carrier -> R.carrier := fun R a b
/// => R.add a (R.neg b)` — matching `Rat.sub`'s/`Int.sub`'s own definition
/// exactly (`group.rs`'s `declare_subtraction` module doc).
fn build_sub(k: &mut Kernel, ring: &RecordNames) -> (ExprId, ExprId) {
    use structures::idx::ring::{ADD, CARRIER, NEG};
    const R_FV: u64 = 22_200;
    const A_FV: u64 = 22_201;
    const B_FV: u64 = 22_202;

    let ind_ty = k.const_(ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let add = sel(k, ring, ADD, r);
    let neg = sel(k, ring, NEG, r);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let nb = k.app(neg, b);
    let result = app2(k, add, a, nb);

    let value = lam_over(k, B_FV, carrier, result);
    let value = lam_over(k, A_FV, carrier, value);
    let value = lam_over(k, R_FV, ind_ty, value);

    let ty = {
        let inner = arrow(k, carrier, carrier);
        let t = arrow(k, carrier, inner);
        pi_over(k, R_FV, ind_ty, t)
    };
    (ty, value)
}

/// `Alg.sub_self : forall (R:Ring)(x:R.carrier), Alg.sub R x x=R.zero` --
/// ADR-1590, DERIVED from `AlgS.sub_self` applied at `AlgS.Ring.ofAlg R`
/// (mirroring `build_ring_mul_zero`'s derivation exactly, and the same
/// discipline). `Alg.sub`/`AlgS.sub` are two independently-declared
/// `Definition`s of the identical shape (`fun R a b => R.add a (R.neg b)`),
/// so `Alg.sub R x x` and `AlgS.sub (ofAlg R) x x` both delta/iota-reduce to
/// the SAME normal form `R.add x (R.neg x)` -- confirmed by the kernel's own
/// `def_eq`, not assumed. The stated `ty` below is unchanged from the
/// hand-proof version (`fun R x => R.negAdd x`, still `AlgS.sub_self`'s own
/// proof body one level up), so the declared type stays byte-identical.
fn build_sub_self(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    ring: &RecordNames,
    sub_name: NameId,
    ring_ofalg: NameId,
    algs_sub_self: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::ring::{CARRIER, ZERO};
    const R_FV: u64 = 22_210;
    const X_FV: u64 = 22_211;

    let ind_ty = k.const_(ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let zero = sel(k, ring, ZERO, r);
    let x = k.fvar(X_FV);

    let ofalg = k.const_(ring_ofalg, vec![]);
    let rs = k.app(ofalg, r); // AlgS.Ring.ofAlg R : AlgS.Ring
    let algs_sub_self_c = k.const_(algs_sub_self, vec![]);
    let result = app2(k, algs_sub_self_c, rs, x); // : (ofAlg R).equiv (AlgS.sub (ofAlg R) x x) zero

    let value = lam_over(k, X_FV, carrier, result);
    let value = lam_over(k, R_FV, ind_ty, value);

    let sub_c = k.const_(sub_name, vec![]);
    let sub_r_x_x = {
        let e1 = k.app(sub_c, r);
        let e2 = k.app(e1, x);
        k.app(e2, x)
    };
    let concl = eq_of(k, lg, l1, carrier, sub_r_x_x, zero);
    let ty = pi_over(k, X_FV, carrier, concl);
    let ty = pi_over(k, R_FV, ind_ty, ty);
    (ty, value)
}

/// `Alg.mul_neg_one : forall (R:Ring)(x:R.carrier), R.mul x (R.neg R.one) =
/// R.neg x`. Built by projecting `R`'s additive structure down to a `Group`
/// (`Ring.toCommGroup` then `CommGroup.toGroup`) and applying
/// `Alg.groupInvUnique` there, rather than deriving `mul a (neg b) = neg (mul
/// a b)` directly — the payoff `Alg.CommMonoid.toMonoid`/etc. exist for.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn build_mul_neg_one(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    ring: &RecordNames,
    ring_mul_zero: NameId,
    group_inv_unique: NameId,
    ring_to_comm_group: NameId,
    comm_group_to_group: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::ring::{ADD, CARRIER, DISTRIB_L, MUL, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO};
    const R_FV: u64 = 22_300;
    const X_FV: u64 = 22_301;
    const S1: u64 = 22_302;
    const S2: u64 = 22_303;

    let ind_ty = k.const_(ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let zero = sel(k, ring, ZERO, r);
    let one = sel(k, ring, ONE, r);
    let add = sel(k, ring, ADD, r);
    let mul = sel(k, ring, MUL, r);
    let neg = sel(k, ring, NEG, r);
    let neg_add = sel(k, ring, NEG_ADD, r);
    let distrib_l = sel(k, ring, DISTRIB_L, r);
    let mul_one_r = sel(k, ring, MUL_ONE_R, r);

    let x = k.fvar(X_FV);
    let neg_one = k.app(neg, one);
    let a = app2(k, mul, x, neg_one); // A := mul x (neg one)

    // EQ_B : add (neg one) one = zero  (invL at `one`, from Alg.ringMulZero's
    // group -- built inline the same way `derive_inv_left` does, but we
    // already have `neg_add` at `one` directly and need `add_comm`; Ring
    // carries `addComm` at index ADD_COMM).
    let add_comm = sel(k, ring, structures::idx::ring::ADD_COMM, r);
    let eq_b = derive_inv_left(
        k, lg, l1, carrier, zero, add, neg, add_comm, neg_add, S1, S2,
    );
    let eq_b_at_one = k.app(eq_b, one); // : add (neg one) one = zero

    // EQ_A : mul x (add (neg one) one) = add (mul x (neg one)) (mul x one)
    let neg_one_plus_one = app2(k, add, neg_one, one);
    let mul_x_one = app2(k, mul, x, one);
    let eq_a = {
        let e1 = k.app(distrib_l, x);
        let e2 = k.app(e1, neg_one);
        k.app(e2, one)
    }; // : mul x (add (neg one) one) = add (mul x (neg one)) (mul x one)

    // EQ_C : mul x (add (neg one) one) = zero
    let mul_x_negoneplusone = app2(k, mul, x, neg_one_plus_one);
    let mul_x_zero = app2(k, mul, x, zero);
    let congr_b = congr_arg(
        k,
        lg,
        l1,
        carrier,
        neg_one_plus_one,
        zero,
        eq_b_at_one,
        S1,
        &|k2, w| app2(k2, mul, x, w),
    ); // : mul x (add (neg one) one) = mul x zero
    let ring_mul_zero_c = k.const_(ring_mul_zero, vec![]);
    let rmz_x = {
        let e1 = k.app(ring_mul_zero_c, r);
        k.app(e1, x)
    }; // : mul x zero = zero
    let eq_c = trans_of(
        k,
        lg,
        l1,
        carrier,
        mul_x_negoneplusone,
        mul_x_zero,
        zero,
        congr_b,
        rmz_x,
        S2,
    );

    // EQ_D : add (mul x (neg one)) (mul x one) = zero
    let mul_a_mulxone = app2(k, add, a, mul_x_one);
    let symm_eq_a = symm_of(k, lg, l1, carrier, mul_x_negoneplusone, mul_a_mulxone, eq_a);
    let eq_d = trans_of(
        k,
        lg,
        l1,
        carrier,
        mul_a_mulxone,
        mul_x_negoneplusone,
        zero,
        symm_eq_a,
        eq_c,
        S1,
    );

    // FACT1 : add A x = zero, via congr(mulOneR x) on EQ_D.
    let mul_one_r_x = k.app(mul_one_r, x); // : mul x one = x
    let congr_step = congr_arg(
        k,
        lg,
        l1,
        carrier,
        mul_x_one,
        x,
        mul_one_r_x,
        S2,
        &|k2, w| app2(k2, add, a, w),
    ); // : add A (mul x one) = add A x
    let add_a_x = app2(k, add, a, x);
    let symm_congr_step = symm_of(k, lg, l1, carrier, mul_a_mulxone, add_a_x, congr_step);
    let fact1 = trans_of(
        k,
        lg,
        l1,
        carrier,
        add_a_x,
        mul_a_mulxone,
        zero,
        symm_congr_step,
        eq_d,
        S1,
    );

    // G := CommGroup.toGroup (Ring.toCommGroup R) : Group, additive.
    let g = {
        let e1 = k.const_(ring_to_comm_group, vec![]);
        let cg = k.app(e1, r);
        let e2 = k.const_(comm_group_to_group, vec![]);
        k.app(e2, cg)
    };

    let neg_x = k.app(neg, x);
    let h2 = k.app(neg_add, x); // : add x (neg x) = zero

    let thm = k.const_(group_inv_unique, vec![]);
    let applied = {
        let e1 = k.app(thm, g);
        let e2 = k.app(e1, x);
        let e3 = k.app(e2, a);
        let e4 = k.app(e3, neg_x);
        let e5 = k.app(e4, fact1);
        k.app(e5, h2)
    }; // : A = neg x

    let value = lam_over(k, X_FV, carrier, applied);
    let value = lam_over(k, R_FV, ind_ty, value);

    let concl = eq_of(k, lg, l1, carrier, a, neg_x);
    let ty = pi_over(k, X_FV, carrier, concl);
    let ty = pi_over(k, R_FV, ind_ty, ty);
    (ty, value)
}

// ---------------------------------------------------------------------------
// `Alg.npow` / `Alg.pow_add` (deliverable 3, monoid power).
// ---------------------------------------------------------------------------

/// `Nat.rec.{0} motive base step target`, a `Prop`-valued induction.
#[allow(clippy::too_many_arguments)]
pub(crate) fn nat_rec_prop(
    k: &mut Kernel,
    nat_rec: NameId,
    nat_ty: ExprId,
    n_fv: u64,
    j_fv: u64,
    ih_fv: u64,
    motive_body: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
    base: &dyn Fn(&mut Kernel) -> ExprId,
    step: &dyn Fn(&mut Kernel, ExprId, ExprId) -> ExprId,
    target: ExprId,
) -> ExprId {
    let anon = k.anon();
    let n = k.fvar(n_fv);
    let mb = motive_body(k, n);
    let motive = lam_over(k, n_fv, nat_ty, mb);
    let _ = anon;
    let base_term = base(k);
    let step_term = {
        let j = k.fvar(j_fv);
        let hyp_ty = motive_body(k, j);
        let ih = k.fvar(ih_fv);
        let body = step(k, j, ih);
        let inner = lam_over(k, ih_fv, hyp_ty, body);
        lam_over(k, j_fv, nat_ty, inner)
    };
    let z = k.level_zero();
    let rec_c = k.const_(nat_rec, vec![z]);
    let e = k.app(rec_c, motive);
    let e = k.app(e, base_term);
    let e = k.app(e, step_term);
    k.app(e, target)
}

/// `Alg.npow : Pi (M:Monoid), M.carrier -> Nat -> M.carrier`, `npow M x 0 =
/// M.e`, `npow M x (succ n) = M.op (npow M x n) x` — RIGHT-multiply by `x`,
/// matching `Rat.pow`'s/`Int.pow`'s own recursion convention
/// (`polynomial.rs::declare_pow`: `pow a (succ j) = mul (pow a j) a`).
fn build_npow(
    k: &mut Kernel,
    l1: LevelId,
    monoid: &RecordNames,
    nat_rec: NameId,
    nat_ty: ExprId,
) -> (ExprId, ExprId) {
    use structures::idx::monoid::{CARRIER, E, OP};
    const M_FV: u64 = 22_400;
    const X_FV: u64 = 22_401;
    const N_FV: u64 = 22_402;
    const NP_FV: u64 = 22_403;
    const IH_FV: u64 = 22_404;
    let anon = k.anon();

    let ind_ty = k.const_(monoid.ind, vec![]);
    let m = k.fvar(M_FV);
    let carrier = sel(k, monoid, CARRIER, m);
    let e = sel(k, monoid, E, m);
    let op = sel(k, monoid, OP, m);
    let x_ty = carrier;
    let x = k.fvar(X_FV);

    let motive = k.lam(anon, nat_ty, carrier, BinderInfo::Default);
    let step = {
        let ih = k.fvar(IH_FV);
        let body = app2(k, op, ih, x);
        let inner = lam_over(k, IH_FV, carrier, body);
        lam_over(k, NP_FV, nat_ty, inner)
    };
    let rec_c = k.const_(nat_rec, vec![l1]);
    let rec_applied = {
        let e1 = k.app(rec_c, motive);
        let e2 = k.app(e1, e);
        k.app(e2, step)
    };
    let n = k.fvar(N_FV);
    let result = k.app(rec_applied, n);
    let value = lam_over(k, N_FV, nat_ty, result);
    let value = lam_over(k, X_FV, x_ty, value);
    let value = lam_over(k, M_FV, ind_ty, value);

    let ty = {
        let inner = arrow(k, nat_ty, carrier);
        let t = arrow(k, carrier, inner);
        pi_over(k, M_FV, ind_ty, t)
    };
    (ty, value)
}

/// `Alg.pow_add : forall (M:Monoid)(x:M.carrier)(m n:Nat), npow M x (add m
/// n) = M.op (npow M x m) (npow M x n)`. Induction on `n` (the argument
/// `Nat.add` recurses on): base needs only `identR`; the step needs only
/// `assoc` and the induction hypothesis, no self-commutation lemma, because
/// `npow`'s own recursion is RIGHT-multiplying (matching `add`'s own
/// recursion direction).
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn build_pow_add(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    monoid: &RecordNames,
    nat_rec: NameId,
    nat_ty: ExprId,
    nat_zero: ExprId,
    nat_add: NameId,
    npow_name: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::monoid::{ASSOC, CARRIER, IDENT_R, OP};
    const M_FV: u64 = 22_450;
    const X_FV: u64 = 22_451;
    const MM_FV: u64 = 22_452;
    const N_FV: u64 = 22_453;
    const J_FV: u64 = 22_454;
    const IH_FV: u64 = 22_455;
    const S1: u64 = 22_456;

    let ind_ty = k.const_(monoid.ind, vec![]);
    let m = k.fvar(M_FV);
    let carrier = sel(k, monoid, CARRIER, m);
    let op = sel(k, monoid, OP, m);
    let assoc = sel(k, monoid, ASSOC, m);
    let ident_r = sel(k, monoid, IDENT_R, m);
    let x = k.fvar(X_FV);
    let mm = k.fvar(MM_FV);

    let npow_of = |k2: &mut Kernel, nval: ExprId| -> ExprId {
        let c = k2.const_(npow_name, vec![]);
        let e1 = k2.app(c, m);
        let e2 = k2.app(e1, x);
        k2.app(e2, nval)
    };
    let add_of = |k2: &mut Kernel, a: ExprId, b: ExprId| -> ExprId {
        let c = k2.const_(nat_add, vec![]);
        app2(k2, c, a, b)
    };

    let np_m = npow_of(k, mm);

    let motive_body = |k2: &mut Kernel, nvar: ExprId| -> ExprId {
        let add_mm_n = add_of(k2, mm, nvar);
        let lhs = npow_of(k2, add_mm_n);
        let np_n = npow_of(k2, nvar);
        let rhs = app2(k2, op, np_m, np_n);
        eq_of(k2, lg, l1, carrier, lhs, rhs)
    };

    let base = |k2: &mut Kernel| -> ExprId {
        let op_npm_e = {
            let e_sel = sel(k2, monoid, structures::idx::monoid::E, m);
            app2(k2, op, np_m, e_sel)
        };
        let ident_r_np_m = k2.app(ident_r, np_m); // : op np_m e = np_m
        symm_of(k2, lg, l1, carrier, op_npm_e, np_m, ident_r_np_m)
    };

    let step = |k2: &mut Kernel, j: ExprId, ih: ExprId| -> ExprId {
        let np_j = npow_of(k2, j);
        let add_mm_j = add_of(k2, mm, j);
        let np_addmmj = npow_of(k2, add_mm_j);
        let op_npm_npj = app2(k2, op, np_m, np_j);
        // step1 : op np_addmmj x = op (op np_m np_j) x  (congr ih)
        let step1 = congr_arg(
            k2,
            lg,
            l1,
            carrier,
            np_addmmj,
            op_npm_npj,
            ih,
            S1,
            &|k3, w| app2(k3, op, w, x),
        );
        // assoc_term : op (op np_m np_j) x = op np_m (op np_j x)
        let assoc_term = {
            let e1 = k2.app(assoc, np_m);
            let e2 = k2.app(e1, np_j);
            k2.app(e2, x)
        };
        let lhs0 = app2(k2, op, np_addmmj, x);
        let mid = app2(k2, op, op_npm_npj, x);
        let rhs0 = {
            let inner = app2(k2, op, np_j, x);
            app2(k2, op, np_m, inner)
        };
        trans_of(k2, lg, l1, carrier, lhs0, mid, rhs0, step1, assoc_term, S1)
    };

    let n_target = k.fvar(N_FV);
    let induction = nat_rec_prop(
        k,
        nat_rec,
        nat_ty,
        N_FV,
        J_FV,
        IH_FV,
        &motive_body,
        &base,
        &step,
        n_target,
    );

    let value = lam_over(k, N_FV, nat_ty, induction);
    let value = lam_over(k, MM_FV, nat_ty, value);
    let value = lam_over(k, X_FV, carrier, value);
    let value = lam_over(k, M_FV, ind_ty, value);

    let n_free = k.fvar(N_FV);
    let concl = motive_body(k, n_free);
    let ty = pi_over(k, N_FV, nat_ty, concl);
    let ty = pi_over(k, MM_FV, nat_ty, ty);
    let ty = pi_over(k, X_FV, carrier, ty);
    let ty = pi_over(k, M_FV, ind_ty, ty);
    let _ = nat_zero;
    (ty, value)
}

// ---------------------------------------------------------------------------
// `Alg.mul_le_mul_of_nonneg_left` (deliverable 5, `OrderedRing`).
// ---------------------------------------------------------------------------

/// `Alg.mul_le_mul_of_nonneg_left : forall (R:OrderedRing)(a b c:R.carrier),
/// R.le R.zero a -> R.le b c -> R.le (R.mul a b)(R.mul a c)`. `d := add (neg
/// b) c` is `>= 0` (`add_le_add_left` + a transport along the derived `add
/// (neg b) b = zero`); `b + d = c` (assoc + `negAdd` + a derived left-unit);
/// so `a*c = a*b + a*d` (distribL); and `a*d >= 0` (`mul_nonneg`), so `a*b <=
/// a*b + a*d = a*c` (`add_le_add_left` again).
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn build_mul_le_mul_of_nonneg_left(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    ordered_ring: &RecordNames,
) -> (ExprId, ExprId) {
    use structures::idx::ordered_ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_LE_ADD_LEFT, ADD_ZERO, CARRIER, DISTRIB_L, LE, MUL,
        MUL_NONNEG, NEG, NEG_ADD, ZERO,
    };
    const R_FV: u64 = 22_500;
    const A_FV: u64 = 22_501;
    const B_FV: u64 = 22_502;
    const C_FV: u64 = 22_503;
    const H1_FV: u64 = 22_504;
    const H2_FV: u64 = 22_505;
    const S1: u64 = 22_506;
    const S2: u64 = 22_507;
    const S3: u64 = 22_508;

    let ind_ty = k.const_(ordered_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, ordered_ring, CARRIER, r);
    let zero = sel(k, ordered_ring, ZERO, r);
    let add = sel(k, ordered_ring, ADD, r);
    let mul = sel(k, ordered_ring, MUL, r);
    let neg = sel(k, ordered_ring, NEG, r);
    let add_assoc = sel(k, ordered_ring, ADD_ASSOC, r);
    let add_comm = sel(k, ordered_ring, ADD_COMM, r);
    let add_zero = sel(k, ordered_ring, ADD_ZERO, r);
    let neg_add = sel(k, ordered_ring, NEG_ADD, r);
    let distrib_l = sel(k, ordered_ring, DISTRIB_L, r);
    let le = sel(k, ordered_ring, LE, r);
    let add_le_add_left = sel(k, ordered_ring, ADD_LE_ADD_LEFT, r);
    let mul_nonneg = sel(k, ordered_ring, MUL_NONNEG, r);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let h1_ty = app2(k, le, zero, a); // le zero a
    let h2_ty = app2(k, le, b, c); // le b c
    let h1 = k.fvar(H1_FV);
    let h2 = k.fvar(H2_FV);

    let neg_b = k.app(neg, b);
    let d = app2(k, add, neg_b, c);

    // raw : le (add neg_b b) d, via add_le_add_left(b,c,neg_b,h2).
    let raw = {
        let e1 = k.app(add_le_add_left, b);
        let e2 = k.app(e1, c);
        let e3 = k.app(e2, neg_b);
        k.app(e3, h2)
    };
    let add_negb_b = app2(k, add, neg_b, b);

    // invl_b : add neg_b b = zero
    let invl_b = derive_inv_left(
        k, lg, l1, carrier, zero, add, neg, add_comm, neg_add, S1, S2,
    );
    let invl_b_at_b = k.app(invl_b, b);

    // d_nonneg : le zero d
    let d_nonneg = subst(
        k,
        lg,
        l1,
        carrier,
        add_negb_b,
        zero,
        invl_b_at_b,
        S3,
        &|k2, w| app2(k2, le, w, d),
        raw,
    );

    // b_plus_d_eq_c : add b d = c
    let add_b_d = app2(k, add, b, d);
    let add_b_negb = app2(k, add, b, neg_b);
    let assoc_b_negb_c = {
        let e1 = k.app(add_assoc, b);
        let e2 = k.app(e1, neg_b);
        k.app(e2, c)
    }; // : add (add b neg_b) c = add b (add neg_b c) = add b d
    let add_addbnegb_c = app2(k, add, add_b_negb, c);
    let step_a = symm_of(k, lg, l1, carrier, add_addbnegb_c, add_b_d, assoc_b_negb_c);
    let neg_add_b = k.app(neg_add, b); // : add b neg_b = zero
    let add_zero_c = app2(k, add, zero, c);
    let step_b = congr_arg(
        k,
        lg,
        l1,
        carrier,
        add_b_negb,
        zero,
        neg_add_b,
        S1,
        &|k2, w| app2(k2, add, w, c),
    ); // : add (add b neg_b) c = add zero c
    let step_ab = trans_of(
        k,
        lg,
        l1,
        carrier,
        add_b_d,
        add_addbnegb_c,
        add_zero_c,
        step_a,
        step_b,
        S2,
    );
    let ident_l_add = {
        let a_fv = 22_509_u64;
        let sc_fv = 22_510_u64;
        derive_left_unit(
            k, lg, l1, carrier, add, zero, add_comm, add_zero, a_fv, sc_fv,
        )
    };
    let step_c = k.app(ident_l_add, c); // : add zero c = c
    let b_plus_d_eq_c = trans_of(
        k, lg, l1, carrier, add_b_d, add_zero_c, c, step_ab, step_c, S3,
    );

    // a_c_eq_ab_plus_ad : mul a c = add (mul a b) (mul a d)
    let mul_a_c = app2(k, mul, a, c);
    let mul_a_bd = app2(k, mul, a, add_b_d);
    let symm_bd = symm_of(k, lg, l1, carrier, add_b_d, c, b_plus_d_eq_c); // : c = add b d
    let congr_c = congr_arg(k, lg, l1, carrier, c, add_b_d, symm_bd, S1, &|k2, w| {
        app2(k2, mul, a, w)
    }); // : mul a c = mul a (add b d)
    let distrib_term = {
        let e1 = k.app(distrib_l, a);
        let e2 = k.app(e1, b);
        k.app(e2, d)
    }; // : mul a (add b d) = add (mul a b) (mul a d)
    let mul_a_b = app2(k, mul, a, b);
    let mul_a_d = app2(k, mul, a, d);
    let add_mab_mad = app2(k, add, mul_a_b, mul_a_d);
    let a_c_eq_ab_plus_ad = trans_of(
        k,
        lg,
        l1,
        carrier,
        mul_a_c,
        mul_a_bd,
        add_mab_mad,
        congr_c,
        distrib_term,
        S2,
    );

    // ad_nonneg : le zero (mul a d)
    let ad_nonneg = {
        let e1 = k.app(mul_nonneg, a);
        let e2 = k.app(e1, d);
        let e3 = k.app(e2, h1);
        k.app(e3, d_nonneg)
    };

    // raw2 : le (add mul_a_b zero) (add mul_a_b mul_a_d), via
    // add_le_add_left(zero, mul_a_d, mul_a_b, ad_nonneg).
    let raw2 = {
        let e1 = k.app(add_le_add_left, zero);
        let e2 = k.app(e1, mul_a_d);
        let e3 = k.app(e2, mul_a_b);
        k.app(e3, ad_nonneg)
    };
    let mul_ab_zero = app2(k, add, mul_a_b, zero);

    // transport LHS via addZero(mul_a_b) : add mul_a_b zero = mul_a_b
    let add_zero_mab = k.app(add_zero, mul_a_b);
    let raw3 = subst(
        k,
        lg,
        l1,
        carrier,
        mul_ab_zero,
        mul_a_b,
        add_zero_mab,
        S1,
        &|k2, w| app2(k2, le, w, add_mab_mad),
        raw2,
    );
    // transport RHS via symm(a_c_eq_ab_plus_ad) : add mul_a_b mul_a_d = mul a c
    let symm_ac = symm_of(k, lg, l1, carrier, mul_a_c, add_mab_mad, a_c_eq_ab_plus_ad);
    let result = subst(
        k,
        lg,
        l1,
        carrier,
        add_mab_mad,
        mul_a_c,
        symm_ac,
        S2,
        &|k2, w| app2(k2, le, mul_a_b, w),
        raw3,
    );

    let value = lam_over(k, H2_FV, h2_ty, result);
    let value = lam_over(k, H1_FV, h1_ty, value);
    let value = lam_over(k, C_FV, carrier, value);
    let value = lam_over(k, B_FV, carrier, value);
    let value = lam_over(k, A_FV, carrier, value);
    let value = lam_over(k, R_FV, ind_ty, value);

    let concl = app2(k, le, mul_a_b, mul_a_c);
    let ty = pi_over(k, H2_FV, h2_ty, concl);
    let ty = pi_over(k, H1_FV, h1_ty, ty);
    let ty = pi_over(k, C_FV, carrier, ty);
    let ty = pi_over(k, B_FV, carrier, ty);
    let ty = pi_over(k, A_FV, carrier, ty);
    let ty = pi_over(k, R_FV, ind_ty, ty);
    (ty, value)
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AlgebraExtNames {
    pub comm_monoid_to_monoid: NameId,
    pub group_to_monoid: NameId,
    pub comm_group_to_group: NameId,
    pub ring_to_monoid: NameId,
    pub ring_to_comm_group: NameId,
    pub comm_ring_to_ring: NameId,
    pub field_to_comm_ring: NameId,
    pub int_ordered_ring: NameId,
    pub rat_ordered_ring: NameId,
    pub mul_left_cancel: NameId,
    pub neg_neg: NameId,
    pub sub: NameId,
    pub sub_self: NameId,
    pub mul_neg_one: NameId,
    pub npow: NameId,
    pub pow_add: NameId,
    pub mul_le_mul_of_nonneg_left: NameId,
}

fn alg_root(k: &mut Kernel) -> NameId {
    let anon = k.anon();
    k.name_str(anon, "Alg")
}

pub(crate) fn intern_algebra_ext(k: &mut Kernel) -> AlgebraExtNames {
    let alg = alg_root(k);
    AlgebraExtNames {
        comm_monoid_to_monoid: {
            let root = k.name_str(alg, "CommMonoid");
            k.name_str(root, "toMonoid")
        },
        group_to_monoid: {
            let root = k.name_str(alg, "Group");
            k.name_str(root, "toMonoid")
        },
        comm_group_to_group: {
            let root = k.name_str(alg, "CommGroup");
            k.name_str(root, "toGroup")
        },
        ring_to_monoid: {
            let root = k.name_str(alg, "Ring");
            k.name_str(root, "toMonoid")
        },
        ring_to_comm_group: {
            let root = k.name_str(alg, "Ring");
            k.name_str(root, "toCommGroup")
        },
        comm_ring_to_ring: {
            let root = k.name_str(alg, "CommRing");
            k.name_str(root, "toRing")
        },
        field_to_comm_ring: {
            let root = k.name_str(alg, "Field");
            k.name_str(root, "toCommRing")
        },
        int_ordered_ring: {
            let root = k.name_str(alg, "Int");
            k.name_str(root, "orderedRing")
        },
        rat_ordered_ring: {
            let root = k.name_str(alg, "Rat");
            k.name_str(root, "orderedRing")
        },
        mul_left_cancel: k.name_str(alg, "mul_left_cancel"),
        neg_neg: k.name_str(alg, "neg_neg"),
        sub: k.name_str(alg, "sub"),
        sub_self: k.name_str(alg, "sub_self"),
        mul_neg_one: k.name_str(alg, "mul_neg_one"),
        npow: k.name_str(alg, "npow"),
        pow_add: k.name_str(alg, "pow_add"),
        mul_le_mul_of_nonneg_left: k.name_str(alg, "mul_le_mul_of_nonneg_left"),
    }
}

pub(crate) fn declare_algebra_ext_all(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: &RatPrelude,
    st: &structures::StructuresNames,
    ax: &super::algebra_instances::AlgebraNames,
    names: &AlgebraExtNames,
) -> Result<(), KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    declare_projections_all(k, lg, l1, st, names)?;
    declare_ordered_ring_instances(k, lg, l1, p, st, names)?;

    // ADR-1587: `Alg.mul_left_cancel` is declared earlier, at the very start
    // of the whole build (`nat_prelude::structures::declare_mul_left_cancel_early`,
    // called right after the structures spine) -- NOT here, to let
    // `Int.add_left_cancel` retire to it without violating ADR-1581's
    // build-position rule. `names.mul_left_cancel`'s `name_str` interning is
    // idempotent and still resolves to that earlier declaration.
    {
        let (ty, value) = build_neg_neg(k, lg, l1, &st.group, ax.group_inv_unique);
        k.add_declaration(Declaration::Theorem {
            name: names.neg_neg,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_sub(k, &st.ring);
        k.add_declaration(Declaration::Definition {
            name: names.sub,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    {
        let extra = &p.int.nat.structures_s_extra;
        let (ty, value) = build_sub_self(
            k,
            lg,
            l1,
            &st.ring,
            names.sub,
            extra.ring_ofalg,
            extra.sub_self,
        );
        k.add_declaration(Declaration::Theorem {
            name: names.sub_self,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_mul_neg_one(
            k,
            lg,
            l1,
            &st.ring,
            ax.ring_mul_zero,
            ax.group_inv_unique,
            names.ring_to_comm_group,
            names.comm_group_to_group,
        );
        k.add_declaration(Declaration::Theorem {
            name: names.mul_neg_one,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    let nat_ty = k.const_(p.int.nat.nat, vec![]);
    let nat_zero = k.const_(p.int.nat.zero, vec![]);
    let nat_add = p.int.nat.add;
    let nat_rec = p.int.nat.rec;

    {
        let (ty, value) = build_npow(k, l1, &st.monoid, nat_rec, nat_ty);
        k.add_declaration(Declaration::Definition {
            name: names.npow,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    {
        let (ty, value) = build_pow_add(
            k, lg, l1, &st.monoid, nat_rec, nat_ty, nat_zero, nat_add, names.npow,
        );
        k.add_declaration(Declaration::Theorem {
            name: names.pow_add,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_mul_le_mul_of_nonneg_left(k, lg, l1, &st.ordered_ring);
        k.add_declaration(Declaration::Theorem {
            name: names.mul_le_mul_of_nonneg_left,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

#[cfg(test)]
mod algebra_ext_tests {
    use super::*;
    use crate::build_rat_prelude;
    use crate::nat_prelude::structures::refl_of;

    /// Deliverable 2's evaluation test: project `Int.commRing` down to a
    /// `Monoid` (`CommRing.toRing` then `Ring.toMonoid`, multiplicative) and
    /// read `mulOneR`'s type off the projection by REDUCTION — compared
    /// against `Int.mul_one`'s own rendered type, not a doc comment. The
    /// negative control: the projected carrier is `Int` ITSELF, not a fresh
    /// opaque type (a projection that silently produced an unrelated
    /// carrier would still type-check as `Monoid`, since `carrier : Sort 1`
    /// admits anything).
    #[test]
    fn int_comm_ring_projects_to_monoid_and_mul_one_reduces() {
        use structures::idx::monoid::{CARRIER, IDENT_R};
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");

        let int_comm_ring = k.const_(p.algebra.int_comm_ring, vec![]);
        let to_ring = k.const_(p.algebra_ext.comm_ring_to_ring, vec![]);
        let ring_val = k.app(to_ring, int_comm_ring);
        let to_monoid = k.const_(p.algebra_ext.ring_to_monoid, vec![]);
        let monoid_val = k.app(to_monoid, ring_val);

        let carrier = sel(&mut k, &p.int.nat.structures.monoid, CARRIER, monoid_val);
        let int_ty = k.const_(p.int.z, vec![]);
        assert!(
            k.def_eq(carrier, int_ty),
            "negative control: the projected Monoid's carrier must be Int \
             itself, not a fresh/opaque carrier"
        );

        let ident_r = sel(&mut k, &p.int.nat.structures.monoid, IDENT_R, monoid_val);
        let ty = k
            .infer(ident_r)
            .expect("projected selector must type-check");
        let mul_one_c = k.const_(p.int.mul_one, vec![]);
        let expected_ty = k.infer(mul_one_c).expect("Int.mul_one must exist");
        assert!(
            k.def_eq(ty, expected_ty),
            "the projected Monoid's identR selector must reduce to exactly \
             Int.mul_one's own type"
        );
    }

    /// `Alg.CommMonoid.toMonoid`/`Alg.CommGroup.toGroup`/`Alg.Field.toCommRing`
    /// composed the other direction: `Alg.monoidIdentUnique
    /// (CommMonoid.toMonoid Nat.commAddMonoid)` type-checks -- the exact
    /// gap ADR-1578 measured (`Alg.monoidIdentUnique` applied directly to a
    /// `CommMonoid` instance is a `TypeMismatch`).
    #[test]
    fn monoid_ident_unique_applies_through_the_comm_monoid_to_monoid_projection() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let thm = k.const_(p.algebra.monoid_ident_unique, vec![]);
        let comm_monoid = k.const_(p.algebra.nat_comm_add_monoid, vec![]);
        let to_monoid = k.const_(p.algebra_ext.comm_monoid_to_monoid, vec![]);
        let monoid_val = k.app(to_monoid, comm_monoid);

        let nat_ty = k.const_(p.int.nat.nat, vec![]);
        let zero = k.const_(p.int.nat.zero, vec![]);
        let h = k.const_(p.int.nat.add_zero, vec![]);
        let applied = {
            let e1 = k.app(thm, monoid_val);
            let e2 = k.app(e1, zero);
            k.app(e2, h)
        };
        let ty = k
            .infer(applied)
            .expect("must type-check through the projection");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let expect = eq_of(&mut k, &p.int.nat.logic, l1, nat_ty, zero, zero);
        assert!(k.def_eq(ty, expect), "type must be Eq Nat 0 0");
    }

    /// `Alg.sub`'s ENTIRE specification is `fun R a b => R.add a (R.neg b)`,
    /// so the evaluation test that actually discriminates it is a SYMBOLIC
    /// `def_eq` against that exact unfolding (a numeral instance would
    /// exercise nothing `def_eq` does not already exercise, since `sub` does
    /// no recursion) -- confirmed at `Int.ring`, closed over free `a b`.
    #[test]
    fn alg_sub_unfolds_to_add_neg_at_int_ring() {
        use structures::idx::ring::{ADD, CARRIER, NEG};
        const A_FV: u64 = 30_300;
        const B_FV: u64 = 30_301;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let r = k.const_(p.algebra.int_ring, vec![]);
        let carrier = sel(&mut k, &p.int.nat.structures.ring, CARRIER, r);
        let add = sel(&mut k, &p.int.nat.structures.ring, ADD, r);
        let neg = sel(&mut k, &p.int.nat.structures.ring, NEG, r);
        let sub_c = k.const_(p.algebra_ext.sub, vec![]);

        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let lhs = {
            let e1 = k.app(sub_c, r);
            let e2 = k.app(e1, a);
            let e3 = k.app(e2, b);
            lam_over(&mut k, B_FV, carrier, e3)
        };
        let nb = k.app(neg, b);
        let rhs = {
            let e = app2(&mut k, add, a, nb);
            lam_over(&mut k, B_FV, carrier, e)
        };
        let lhs = lam_over(&mut k, A_FV, carrier, lhs);
        let rhs = lam_over(&mut k, A_FV, carrier, rhs);
        assert!(
            k.def_eq(lhs, rhs),
            "Alg.sub R a b must unfold to R.add a (R.neg b)"
        );
    }

    /// `Alg.npow`'s mandatory concrete evaluation (a genuine `Nat.rec`
    /// definition, so a numeral instance exercises real reduction, unlike
    /// `Alg.sub`): at `Nat.commAddMonoid` projected to `Monoid`, `x := 4`,
    /// three DISCRIMINATING small-magnitude points (`n=0,1,2`).
    #[test]
    fn alg_npow_evaluates_at_concrete_nat_add_monoid() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let comm_monoid = k.const_(p.algebra.nat_comm_add_monoid, vec![]);
        let to_monoid = k.const_(p.algebra_ext.comm_monoid_to_monoid, vec![]);
        let m = k.app(to_monoid, comm_monoid);
        let npow_c = k.const_(p.algebra_ext.npow, vec![]);

        let nat_ty = k.const_(p.int.nat.nat, vec![]);
        let num = |k2: &mut Kernel, n: u64| -> ExprId {
            let mut v = k2.const_(p.int.nat.zero, vec![]);
            for _ in 0..n {
                let s = k2.const_(p.int.nat.succ, vec![]);
                v = k2.app(s, v);
            }
            v
        };
        let x4 = num(&mut k, 4);
        let npow_at = |k2: &mut Kernel, n: u64| -> ExprId {
            let e1 = k2.app(npow_c, m);
            let e2 = k2.app(e1, x4);
            let nn = num(k2, n);
            k2.app(e2, nn)
        };
        let _ = nat_ty;

        let r0 = npow_at(&mut k, 0);
        let r1 = npow_at(&mut k, 1);
        let r2 = npow_at(&mut k, 2);
        let expect0 = num(&mut k, 0);
        let expect1 = num(&mut k, 4);
        let expect2 = num(&mut k, 8);
        assert!(k.def_eq(r0, expect0), "npow(M,4,0) must reduce to 0");
        assert!(k.def_eq(r1, expect1), "npow(M,4,1) must reduce to 4");
        assert!(k.def_eq(r2, expect2), "npow(M,4,2) must reduce to 8");
    }

    /// `Alg.mul_left_cancel`, concrete AND symbolic, at `Int.addGroup` and
    /// `Rat.addGroup`.
    #[test]
    fn mul_left_cancel_applies_concretely_and_symbolically() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let thm = k.const_(p.algebra_ext.mul_left_cancel, vec![]);

        // Concrete, at Int: a := 2, b := 3, c := 3, h : add 2 3 = add 2 3
        // (Eq.refl).
        {
            let g = k.const_(p.algebra.int_add_group, vec![]);
            let int_ty = k.const_(p.int.z, vec![]);
            let two = {
                let one = k.const_(p.int.one, vec![]);
                let add = k.const_(p.int.add, vec![]);
                app2(&mut k, add, one, one)
            };
            let three = {
                let one = k.const_(p.int.one, vec![]);
                let add = k.const_(p.int.add, vec![]);
                app2(&mut k, add, two, one)
            };
            let op = sel(
                &mut k,
                &p.int.nat.structures.group,
                structures::idx::group::OP,
                g,
            );
            let add23 = app2(&mut k, op, two, three);
            let refl = refl_of(&mut k, &p.int.nat.logic, l1, int_ty, add23);
            let applied = {
                let e1 = k.app(thm, g);
                let e2 = k.app(e1, two);
                let e3 = k.app(e2, three);
                let e4 = k.app(e3, three);
                k.app(e4, refl)
            };
            let ty = k
                .infer(applied)
                .expect("Int concrete instantiation must type-check");
            let expect = eq_of(&mut k, &p.int.nat.logic, l1, int_ty, three, three);
            assert!(k.def_eq(ty, expect), "Int: type must be Eq 3 3");
        }

        // Symbolic, at Int and Rat: closed over free a b c and the
        // hypothesis fvar.
        for (g_name, carrier_const, label) in [
            (p.algebra.int_add_group, p.int.z, "Int"),
            (p.algebra.rat_add_group, p.int.rat, "Rat"),
        ] {
            const A_FV: u64 = 30_310;
            const B_FV: u64 = 30_311;
            const C_FV: u64 = 30_312;
            const H_FV: u64 = 30_313;
            let g = k.const_(g_name, vec![]);
            let carrier = k.const_(carrier_const, vec![]);
            let op = sel(
                &mut k,
                &p.int.nat.structures.group,
                structures::idx::group::OP,
                g,
            );
            let a = k.fvar(A_FV);
            let b = k.fvar(B_FV);
            let c = k.fvar(C_FV);
            let op_a_b = app2(&mut k, op, a, b);
            let op_a_c = app2(&mut k, op, a, c);
            let hyp = eq_of(&mut k, &p.int.nat.logic, l1, carrier, op_a_b, op_a_c);
            let closed = {
                let h = k.fvar(H_FV);
                let applied = {
                    let e1 = k.app(thm, g);
                    let e2 = k.app(e1, a);
                    let e3 = k.app(e2, b);
                    let e4 = k.app(e3, c);
                    k.app(e4, h)
                };
                let v = lam_over(&mut k, H_FV, hyp, applied);
                let v = lam_over(&mut k, C_FV, carrier, v);
                let v = lam_over(&mut k, B_FV, carrier, v);
                lam_over(&mut k, A_FV, carrier, v)
            };
            k.infer(closed).unwrap_or_else(|e| {
                panic!("{label} symbolic instantiation must type-check: {e:?}")
            });
        }
    }

    /// `Alg.neg_neg`, concrete at `Int.addGroup` (`x := 3`) and symbolic at
    /// `Rat.addGroup`.
    #[test]
    fn neg_neg_applies_concretely_at_int_and_symbolically_at_rat() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let thm = k.const_(p.algebra_ext.neg_neg, vec![]);

        {
            let g = k.const_(p.algebra.int_add_group, vec![]);
            let int_ty = k.const_(p.int.z, vec![]);
            let three = {
                let one = k.const_(p.int.one, vec![]);
                let add = k.const_(p.int.add, vec![]);
                let two = app2(&mut k, add, one, one);
                app2(&mut k, add, two, one)
            };
            let applied = {
                let e1 = k.app(thm, g);
                k.app(e1, three)
            };
            let ty = k
                .infer(applied)
                .expect("Int concrete instantiation must type-check");
            let expect = eq_of(&mut k, &p.int.nat.logic, l1, int_ty, three, three);
            assert!(k.def_eq(ty, expect), "Int: neg(neg 3) must type as Eq 3 3");
        }
        {
            const A_FV: u64 = 30_320;
            let g = k.const_(p.algebra.rat_add_group, vec![]);
            let carrier = k.const_(p.int.rat, vec![]);
            let a = k.fvar(A_FV);
            let applied = {
                let e1 = k.app(thm, g);
                k.app(e1, a)
            };
            let closed = lam_over(&mut k, A_FV, carrier, applied);
            k.infer(closed)
                .expect("Rat symbolic instantiation must type-check");
        }
    }

    /// `Alg.sub_self` and `Alg.mul_neg_one`, symbolic, at `Int.ring` and
    /// `Rat.ring`.
    #[test]
    fn sub_self_and_mul_neg_one_apply_symbolically_at_int_and_rat_rings() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let sub_self_c = k.const_(p.algebra_ext.sub_self, vec![]);
        let mul_neg_one_c = k.const_(p.algebra_ext.mul_neg_one, vec![]);

        for (r_name, carrier_const, label) in [
            (p.algebra.int_ring, p.int.z, "Int"),
            (p.algebra.rat_ring, p.int.rat, "Rat"),
        ] {
            const X_FV: u64 = 30_330;
            let r = k.const_(r_name, vec![]);
            let carrier = k.const_(carrier_const, vec![]);
            let x = k.fvar(X_FV);
            let applied1 = {
                let e1 = k.app(sub_self_c, r);
                k.app(e1, x)
            };
            let closed1 = lam_over(&mut k, X_FV, carrier, applied1);
            k.infer(closed1)
                .unwrap_or_else(|e| panic!("{label} sub_self must type-check: {e:?}"));

            let x2 = k.fvar(X_FV);
            let applied2 = {
                let e1 = k.app(mul_neg_one_c, r);
                k.app(e1, x2)
            };
            let closed2 = lam_over(&mut k, X_FV, carrier, applied2);
            k.infer(closed2)
                .unwrap_or_else(|e| panic!("{label} mul_neg_one must type-check: {e:?}"));
        }
    }

    /// `Alg.pow_add`, symbolic, at `Rat.commMulMonoid` projected to
    /// `Monoid`.
    #[test]
    fn pow_add_applies_symbolically_at_rat_comm_mul_monoid() {
        const X_FV: u64 = 30_340;
        const M_FV: u64 = 30_341;
        const N_FV: u64 = 30_342;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let comm_monoid = k.const_(p.algebra.rat_comm_mul_monoid, vec![]);
        let to_monoid = k.const_(p.algebra_ext.comm_monoid_to_monoid, vec![]);
        let monoid_val = k.app(to_monoid, comm_monoid);
        let thm = k.const_(p.algebra_ext.pow_add, vec![]);
        let rat_ty = k.const_(p.int.rat, vec![]);
        let nat_ty = k.const_(p.int.nat.nat, vec![]);

        let x = k.fvar(X_FV);
        let mm = k.fvar(M_FV);
        let n = k.fvar(N_FV);
        let applied = {
            let e1 = k.app(thm, monoid_val);
            let e2 = k.app(e1, x);
            let e3 = k.app(e2, mm);
            k.app(e3, n)
        };
        let v = lam_over(&mut k, N_FV, nat_ty, applied);
        let v = lam_over(&mut k, M_FV, nat_ty, v);
        let closed = lam_over(&mut k, X_FV, rat_ty, v);
        k.infer(closed)
            .expect("Rat.commMulMonoid instantiation must type-check");
    }

    /// `Alg.mul_le_mul_of_nonneg_left`, symbolic, at `Int.orderedRing` and
    /// `Rat.orderedRing`.
    #[test]
    fn mul_le_mul_of_nonneg_left_applies_symbolically_at_int_and_rat_ordered_rings() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let thm = k.const_(p.algebra_ext.mul_le_mul_of_nonneg_left, vec![]);

        for (r_name, carrier_const, label) in [
            (p.algebra_ext.int_ordered_ring, p.int.z, "Int"),
            (p.algebra_ext.rat_ordered_ring, p.int.rat, "Rat"),
        ] {
            const A_FV: u64 = 30_350;
            const B_FV: u64 = 30_351;
            const C_FV: u64 = 30_352;
            const H1_FV: u64 = 30_353;
            const H2_FV: u64 = 30_354;
            let r = k.const_(r_name, vec![]);
            let carrier = k.const_(carrier_const, vec![]);
            let le = sel(
                &mut k,
                &p.int.nat.structures.ordered_ring,
                structures::idx::ordered_ring::LE,
                r,
            );
            let zero = sel(
                &mut k,
                &p.int.nat.structures.ordered_ring,
                structures::idx::ordered_ring::ZERO,
                r,
            );
            let a = k.fvar(A_FV);
            let b = k.fvar(B_FV);
            let c = k.fvar(C_FV);
            let h1_ty = app2(&mut k, le, zero, a);
            let h2_ty = app2(&mut k, le, b, c);
            let closed = {
                let h1 = k.fvar(H1_FV);
                let h2 = k.fvar(H2_FV);
                let applied = {
                    let e1 = k.app(thm, r);
                    let e2 = k.app(e1, a);
                    let e3 = k.app(e2, b);
                    let e4 = k.app(e3, c);
                    let e5 = k.app(e4, h1);
                    k.app(e5, h2)
                };
                let v = lam_over(&mut k, H2_FV, h2_ty, applied);
                let v = lam_over(&mut k, H1_FV, h1_ty, v);
                let v = lam_over(&mut k, C_FV, carrier, v);
                let v = lam_over(&mut k, B_FV, carrier, v);
                lam_over(&mut k, A_FV, carrier, v)
            };
            k.infer(closed)
                .unwrap_or_else(|e| panic!("{label} instantiation must type-check: {e:?}"));
        }
        let _ = l1;
    }

    // -----------------------------------------------------------------------
    // Deliverable 4: the retirement measurement.
    // -----------------------------------------------------------------------

    /// `Alg.mul_left_cancel` instantiated at `Int.addGroup` (`op := Int.add`)
    /// is EXACTLY `Int.add_left_cancel`'s statement: `forall a b c, add a
    /// b=add a c -> b=c`. Compared by TYPE (not `def_eq` of the terms, since
    /// the generic theorem's proof and the hand proof are different terms).
    #[test]
    fn retirement_int_add_left_cancel() {
        const A_FV: u64 = 30_400;
        const B_FV: u64 = 30_401;
        const C_FV: u64 = 30_402;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let thm = k.const_(p.algebra_ext.mul_left_cancel, vec![]);
        let g = k.const_(p.algebra.int_add_group, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let c = k.fvar(C_FV);
        let generic_applied = {
            let e1 = k.app(thm, g);
            let e2 = k.app(e1, a);
            let e3 = k.app(e2, b);
            k.app(e3, c)
        };
        let generic_closed = {
            let v = generic_applied;
            let v = lam_over(&mut k, C_FV, carrier, v);
            let v = lam_over(&mut k, B_FV, carrier, v);
            lam_over(&mut k, A_FV, carrier, v)
        };
        let generic_ty = k.infer(generic_closed).expect("generic must type-check");

        let hand = k.const_(p.int.add_left_cancel, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_left_cancel must exist");

        assert!(
            k.def_eq(generic_ty, hand_ty),
            "Alg.mul_left_cancel(Int.addGroup) closed over (a,b,c) must have \
             the SAME TYPE as Int.add_left_cancel. ADR-1587: this candidate \
             cleared all three of ADR-1581's checks (no emitter/instance \
             citation, Alg.mul_left_cancel declared before this theorem's \
             own build position, no fact names it) and IS retired -- \
             Int.add_left_cancel's own proof (int_prelude/add_basics.rs) now \
             applies Alg.mul_left_cancel at an inline Group value, so this \
             assertion now exercises the retired proof itself, not merely a \
             measured candidate."
        );
    }

    /// `Alg.neg_neg` instantiated at `Rat.addGroup` is EXACTLY `Rat.neg_neg`.
    /// `Int.neg_neg` has NO retirement target: `int_prelude/gcd.rs`'s
    /// `neg_neg` is a private Rust proof-term HELPER (`pub(super) fn
    /// neg_neg`), never declared as a kernel theorem -- so `Alg.neg_neg`
    /// instantiated at `Int.addGroup` is a NEW top-level fact, not a
    /// retirement.
    #[test]
    fn retirement_rat_neg_neg() {
        const A_FV: u64 = 30_410;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let thm = k.const_(p.algebra_ext.neg_neg, vec![]);
        let g = k.const_(p.algebra.rat_add_group, vec![]);
        let carrier = k.const_(p.int.rat, vec![]);
        let a = k.fvar(A_FV);
        let applied = {
            let e1 = k.app(thm, g);
            k.app(e1, a)
        };
        let generic_closed = lam_over(&mut k, A_FV, carrier, applied);
        let generic_ty = k.infer(generic_closed).expect("generic must type-check");

        let hand = k.const_(p.neg_neg, vec![]);
        let hand_ty = k.infer(hand).expect("Rat.neg_neg must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "Alg.neg_neg(Rat.addGroup) closed over `a` must have the SAME \
             TYPE as Rat.neg_neg"
        );
    }

    /// `Alg.sub_self` instantiated at `Rat.ring` is EXACTLY `Rat.sub_self`
    /// (`Rat.sub`'s own definition IS `add a (neg b)`, matching `Alg.sub`
    /// exactly -- `group.rs`'s `declare_subtraction` module doc).
    #[test]
    fn retirement_rat_sub_self() {
        const X_FV: u64 = 30_420;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let thm = k.const_(p.algebra_ext.sub_self, vec![]);
        let r = k.const_(p.algebra.rat_ring, vec![]);
        let carrier = k.const_(p.int.rat, vec![]);
        let x = k.fvar(X_FV);
        let applied = {
            let e1 = k.app(thm, r);
            k.app(e1, x)
        };
        let generic_closed = lam_over(&mut k, X_FV, carrier, applied);
        let generic_ty = k.infer(generic_closed).expect("generic must type-check");

        let hand = k.const_(p.sub_self, vec![]);
        let hand_ty = k.infer(hand).expect("Rat.sub_self must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "Alg.sub_self(Rat.ring) closed over `x`, with Alg.sub, must \
             have the SAME TYPE as Rat.sub_self"
        );
    }

    /// `Alg.mul_le_mul_of_nonneg_left` instantiated at `Int.orderedRing`/
    /// `Rat.orderedRing` against `Int.mul_le_mul_of_nonneg_left`/
    /// `Rat.mul_le_mul_of_nonneg_left` -- both exist and match exactly.
    #[test]
    fn retirement_mul_le_mul_of_nonneg_left_both_carriers() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let thm = k.const_(p.algebra_ext.mul_le_mul_of_nonneg_left, vec![]);

        for (r_name, carrier_const, hand_name, label) in [
            (
                p.algebra_ext.int_ordered_ring,
                p.int.z,
                p.int.mul_le_mul_of_nonneg_left,
                "Int",
            ),
            (
                p.algebra_ext.rat_ordered_ring,
                p.int.rat,
                p.mul_le_mul_of_nonneg_left,
                "Rat",
            ),
        ] {
            const A_FV: u64 = 30_430;
            const B_FV: u64 = 30_431;
            const C_FV: u64 = 30_432;
            let r = k.const_(r_name, vec![]);
            let carrier = k.const_(carrier_const, vec![]);
            let a = k.fvar(A_FV);
            let b = k.fvar(B_FV);
            let c = k.fvar(C_FV);
            let applied = {
                let e1 = k.app(thm, r);
                let e2 = k.app(e1, a);
                let e3 = k.app(e2, b);
                k.app(e3, c)
            };
            let generic_closed = {
                let v = applied;
                let v = lam_over(&mut k, C_FV, carrier, v);
                let v = lam_over(&mut k, B_FV, carrier, v);
                lam_over(&mut k, A_FV, carrier, v)
            };
            let generic_ty = k
                .infer(generic_closed)
                .unwrap_or_else(|e| panic!("{label} generic must type-check: {e:?}"));
            let hand = k.const_(hand_name, vec![]);
            let hand_ty = k
                .infer(hand)
                .unwrap_or_else(|e| panic!("{label} hand lemma must exist: {e:?}"));
            assert!(
                k.def_eq(generic_ty, hand_ty),
                "{label}: Alg.mul_le_mul_of_nonneg_left(OrderedRing) closed \
                 over (a,b,c) must have the SAME TYPE as the hand lemma"
            );
        }
    }

    /// `Alg.pow_add` at `Rat.commMulMonoid` (projected) vs `Rat.pow_add`: is
    /// `npow` `def_eq` to `Rat.pow`? MEASURED, not asserted -- `npow` and
    /// `Rat.pow` are two independently-built `Nat.rec` instances (the
    /// `Nat.multichoose`/`detR` boundary), so agreement at every value does
    /// not imply syntactic `def_eq`.
    #[test]
    fn measure_npow_vs_rat_pow_agreement_at_rat_comm_mul_monoid() {
        const X_FV: u64 = 30_440;
        const N_FV: u64 = 30_441;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let comm_monoid = k.const_(p.algebra.rat_comm_mul_monoid, vec![]);
        let to_monoid = k.const_(p.algebra_ext.comm_monoid_to_monoid, vec![]);
        let monoid_val = k.app(to_monoid, comm_monoid);
        let rat_ty = k.const_(p.int.rat, vec![]);
        let nat_ty = k.const_(p.int.nat.nat, vec![]);

        let x = k.fvar(X_FV);
        let n = k.fvar(N_FV);
        let npow_c = k.const_(p.algebra_ext.npow, vec![]);
        let npow_closed = {
            let e1 = k.app(npow_c, monoid_val);
            let e2 = k.app(e1, x);
            let v = k.app(e2, n);
            let v = lam_over(&mut k, N_FV, nat_ty, v);
            lam_over(&mut k, X_FV, rat_ty, v)
        };
        let pow_c = k.const_(p.pow, vec![]);
        let pow_closed = {
            let x2 = k.fvar(X_FV);
            let n2 = k.fvar(N_FV);
            let e1 = k.app(pow_c, x2);
            let v = k.app(e1, n2);
            let v = lam_over(&mut k, N_FV, nat_ty, v);
            lam_over(&mut k, X_FV, rat_ty, v)
        };
        let agree = k.def_eq(npow_closed, pow_closed);
        println!(
            "ADR-1584 measurement: Alg.npow(Rat.commMulMonoid,x,n) def_eq \
             Rat.pow(x,n) at symbolic x,n = {agree}"
        );
        // Not asserted either way -- the retirement report records the
        // measured value.
    }

    /// `Alg.mul_neg_one` has no exact-name hand-proved counterpart on either
    /// carrier: `neg_one_mul` (Int) is the MIRRORED LEFT form (`(-1)*x=-x`,
    /// not `x*(-1)=-x`) and there is no `Rat.neg_one_mul`/`Rat.mul_neg_one`
    /// at all. This test confirms the negative rather than assuming it.
    #[test]
    fn mul_neg_one_has_no_retirement_target() {
        // No `field_names` grep here -- this is a compiled-in confirmation
        // that this lane did not invent a name that happens to already
        // exist. If a future prelude adds `Rat.mul_neg_one`, `p.mul_neg_one`
        // below fails to compile (no such field), which is the loud failure
        // we want.
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let _ = k.const_(p.int.neg_one_mul, vec![]); // exists, LEFT form only
    }
}
