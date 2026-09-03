//! ADR-1578, deliverables 3-5: ℕ/ℤ/ℚ instances of the `Alg.*` record spine
//! (`nat_prelude::structures`), three theorems proved once over a record and
//! instantiated at two carriers, and a generic `det_one` over an arbitrary
//! `Alg.CommRing`.
//!
//! Every instance is `<Record>.mk` applied to already-proved `Nat`/`Int`/
//! `Rat` lemma constants — no new arithmetic. Two law fields have no
//! ready-made lemma in the source prelude and are derived once here and
//! reused: `Rat` has no `one_mul` (only `mul_one` + `mul_comm`), and `Int`
//! has no `zero_add` (only `add_zero` + `add_comm`) — both are the same
//! shape, [`derive_left_unit`].
//!
//! `Rat.field`, `Rat.commRing` and `Rat.ring` are three INDEPENDENT record
//! values built from the same underlying `Rat.*` constants — no inheritance,
//! matching ADR-1578's decision.

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
    self, RecordNames, app2, arrow, congr_arg, eq_of, lam_over, pi_over, symm_of, trans_of,
};

// ---------------------------------------------------------------------------
// Small helpers.
// ---------------------------------------------------------------------------

/// The `Alg` root name, recomputed (not stored) -- `name_str` is interned, so
/// this is the SAME `NameId` `nat_prelude::structures::intern_structures_names`
/// produced.
fn alg_root(k: &mut Kernel) -> NameId {
    let anon = k.anon();
    k.name_str(anon, "Alg")
}

/// Apply selector `i` of record `rn` to structure term `s`.
pub(crate) fn sel(k: &mut Kernel, rn: &RecordNames, i: usize, s: ExprId) -> ExprId {
    let c = k.const_(rn.sel(i), vec![]);
    k.app(c, s)
}

/// `<Record>.mk arg0 arg1 ...` in field order.
pub(crate) fn mk_instance(k: &mut Kernel, rn: &RecordNames, args: &[ExprId]) -> ExprId {
    let mut v = k.const_(rn.mk, vec![]);
    for a in args {
        v = k.app(v, *a);
    }
    v
}

fn declare_instance(
    k: &mut Kernel,
    name: NameId,
    rn: &RecordNames,
    args: &[ExprId],
) -> Result<(), KernelError> {
    let ty = k.const_(rn.ind, vec![]);
    let value = mk_instance(k, rn, args);
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// Builds `∀ a, op unit a = a` (a VALUE, i.e. a proof term of that type) from
/// `comm : ∀ x y, op x y = op y x` and `right_unit : ∀ x, op x unit = x`.
/// Reused for `Rat`'s missing `one_mul` and `Int`'s missing `zero_add`.
pub(crate) fn derive_left_unit(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    carrier_ty: ExprId,
    op: ExprId,
    unit: ExprId,
    comm: ExprId,
    right_unit: ExprId,
    a_fv: u64,
    scratch_fv: u64,
) -> ExprId {
    let a = k.fvar(a_fv);
    let op_unit_a = app2(k, op, unit, a);
    let op_a_unit = app2(k, op, a, unit);
    let comm_applied = {
        let c1 = k.app(comm, unit);
        k.app(c1, a)
    }; // : Eq (op unit a) (op a unit)
    let ru_applied = k.app(right_unit, a); // : Eq (op a unit) a
    let body = trans_of(
        k,
        lg,
        l1,
        carrier_ty,
        op_unit_a,
        op_a_unit,
        a,
        comm_applied,
        ru_applied,
        scratch_fv,
    );
    lam_over(k, a_fv, carrier_ty, body)
}

// ---------------------------------------------------------------------------
// Instances.
// ---------------------------------------------------------------------------

/// `Nat.commAddMonoid : Alg.CommMonoid`, `Rat.commMulMonoid : Alg.CommMonoid`,
/// `Int.addGroup` / `Rat.addGroup : Alg.Group`, `Int.ring` / `Rat.ring :
/// Alg.Ring`, `Int.commRing` / `Rat.commRing : Alg.CommRing`, `Rat.field :
/// Alg.Field`.
#[allow(clippy::too_many_lines)]
fn declare_instances(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    p: &RatPrelude,
    st: &structures::StructuresNames,
    names: &AlgebraNames,
) -> Result<(), KernelError> {
    let np = p.int.nat;
    let ip = p.int;

    // --- Nat.commAddMonoid : (Nat, +, 0) -----------------------------------
    {
        use structures::idx::comm_monoid::{ASSOC, CARRIER, COMM, E, IDENT_L, IDENT_R, OP};
        let nat_ty = k.const_(np.nat, vec![]);
        let add = k.const_(np.add, vec![]);
        let zero = k.const_(np.zero, vec![]);
        let assoc = k.const_(np.add_assoc, vec![]);
        let ident_l = k.const_(np.zero_add, vec![]);
        let ident_r = k.const_(np.add_zero, vec![]);
        let comm = k.const_(np.add_comm, vec![]);
        let mut args = vec![ExprId(0); COMM + 1];
        args[CARRIER] = nat_ty;
        args[OP] = add;
        args[E] = zero;
        args[ASSOC] = assoc;
        args[IDENT_L] = ident_l;
        args[IDENT_R] = ident_r;
        args[COMM] = comm;
        declare_instance(k, names.nat_comm_add_monoid, &st.comm_monoid, &args)?;
    }

    // --- Rat.commMulMonoid : (Rat, *, 1) -----------------------------------
    {
        use structures::idx::comm_monoid::{ASSOC, CARRIER, COMM, E, IDENT_L, IDENT_R, OP};
        let rat_ty = k.const_(p.int.rat, vec![]);
        let mul = k.const_(p.int.rat_mul, vec![]);
        let one = k.const_(p.one, vec![]);
        let assoc = k.const_(p.mul_assoc, vec![]);
        let comm = k.const_(p.mul_comm, vec![]);
        let right_unit = k.const_(p.mul_one, vec![]);
        let ident_l = derive_left_unit(
            k, lg, l1, rat_ty, mul, one, comm, right_unit, 20_001, 20_002,
        );
        let mut args = vec![ExprId(0); COMM + 1];
        args[CARRIER] = rat_ty;
        args[OP] = mul;
        args[E] = one;
        args[ASSOC] = assoc;
        args[IDENT_L] = ident_l;
        args[IDENT_R] = right_unit;
        args[COMM] = comm;
        declare_instance(k, names.rat_comm_mul_monoid, &st.comm_monoid, &args)?;
    }

    // --- Int.addGroup : (Int, +, 0, neg) -----------------------------------
    {
        use structures::idx::group::{ASSOC, CARRIER, E, IDENT_L, IDENT_R, INV, INV_L, INV_R, OP};
        let int_ty = k.const_(ip.z, vec![]);
        let add = k.const_(ip.add, vec![]);
        let zero = k.const_(ip.zero, vec![]);
        let neg = k.const_(ip.neg, vec![]);
        let assoc = k.const_(ip.add_assoc, vec![]);
        let comm = k.const_(ip.add_comm, vec![]);
        let right_unit = k.const_(ip.add_zero, vec![]);
        let ident_l = derive_left_unit(
            k, lg, l1, int_ty, add, zero, comm, right_unit, 20_003, 20_004,
        );
        let inv_l = k.const_(ip.add_left_neg, vec![]);
        let inv_r = k.const_(ip.add_neg, vec![]);
        let mut args = vec![ExprId(0); INV_R + 1];
        args[CARRIER] = int_ty;
        args[OP] = add;
        args[E] = zero;
        args[INV] = neg;
        args[ASSOC] = assoc;
        args[IDENT_L] = ident_l;
        args[IDENT_R] = right_unit;
        args[INV_L] = inv_l;
        args[INV_R] = inv_r;
        declare_instance(k, names.int_add_group, &st.group, &args)?;
    }

    // --- Rat.addGroup : (Rat, +, 0, neg) -- every field direct -------------
    {
        use structures::idx::group::{ASSOC, CARRIER, E, IDENT_L, IDENT_R, INV, INV_L, INV_R, OP};
        let rat_ty = k.const_(p.int.rat, vec![]);
        let add = k.const_(p.int.rat_add, vec![]);
        let zero = k.const_(p.zero, vec![]);
        let neg = k.const_(p.int.rat_neg, vec![]);
        let assoc = k.const_(p.add_assoc, vec![]);
        let ident_l = k.const_(p.zero_add, vec![]);
        let ident_r = k.const_(p.add_zero, vec![]);
        let inv_l = k.const_(p.neg_add_cancel, vec![]);
        let inv_r = k.const_(p.add_neg, vec![]);
        let mut args = vec![ExprId(0); INV_R + 1];
        args[CARRIER] = rat_ty;
        args[OP] = add;
        args[E] = zero;
        args[INV] = neg;
        args[ASSOC] = assoc;
        args[IDENT_L] = ident_l;
        args[IDENT_R] = ident_r;
        args[INV_L] = inv_l;
        args[INV_R] = inv_r;
        declare_instance(k, names.rat_add_group, &st.group, &args)?;
    }

    // --- Int.ring -- every field direct ------------------------------------
    let int_ring_args = {
        use structures::idx::ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_ONE_L, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO,
        };
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
        let mut args = vec![ExprId(0); NEG_ADD + 1];
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
        args
    };
    declare_instance(k, names.int_ring, &st.ring, &int_ring_args)?;
    {
        // Int.commRing = Int.ring's 15 fields + mulComm.
        use structures::idx::comm_ring::MUL_COMM;
        let mut args = int_ring_args.clone();
        args.push(k.const_(ip.mul_comm, vec![]));
        debug_assert_eq!(args.len(), MUL_COMM + 1);
        declare_instance(k, names.int_comm_ring, &st.comm_ring, &args)?;
    }

    // --- Rat.ring -- only mulOneL is derived --------------------------------
    let rat_ring_args = {
        use structures::idx::ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_ONE_L, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO,
        };
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
            k, lg, l1, rat_ty, mul, one, mul_comm, mul_one_r, 20_005, 20_006,
        );
        let distrib_l = k.const_(p.left_distrib, vec![]);
        let distrib_r = k.const_(p.right_distrib, vec![]);
        let neg = k.const_(p.int.rat_neg, vec![]);
        let neg_add = k.const_(p.add_neg, vec![]);
        let mut args = vec![ExprId(0); NEG_ADD + 1];
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
        args
    };
    declare_instance(k, names.rat_ring, &st.ring, &rat_ring_args)?;
    let rat_comm_ring_args = {
        use structures::idx::comm_ring::MUL_COMM;
        let mut args = rat_ring_args.clone();
        args.push(k.const_(p.mul_comm, vec![]));
        debug_assert_eq!(args.len(), MUL_COMM + 1);
        args
    };
    declare_instance(k, names.rat_comm_ring, &st.comm_ring, &rat_comm_ring_args)?;
    {
        // Rat.field = Rat.commRing's 16 fields + inv, oneNeZero, mulInv.
        use structures::idx::field::MUL_INV;
        let mut args = rat_comm_ring_args.clone();
        args.push(k.const_(p.inv, vec![]));
        args.push(k.const_(p.one_ne_zero, vec![]));
        args.push(k.const_(p.mul_inv_cancel_of_ne_zero, vec![]));
        debug_assert_eq!(args.len(), MUL_INV + 1);
        declare_instance(k, names.rat_field, &st.field, &args)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Three generic theorems, each proved once over a record.
// ---------------------------------------------------------------------------

/// `Alg.monoidIdentUnique : forall (M : Monoid) (e' : M.carrier), (forall a,
/// M.op a e' = a) -> e' = M.e`. Two substitutions and a `trans` -- the same
/// shape `Nat.group_identity_unique` uses.
fn build_monoid_ident_unique(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    monoid: &RecordNames,
) -> (ExprId, ExprId) {
    use structures::idx::monoid::{CARRIER, E, IDENT_L, OP};
    const M_FV: u64 = 21_000;
    const EP_FV: u64 = 21_001;
    const A_FV: u64 = 21_002;
    const H_FV: u64 = 21_003;
    const SCRATCH_FV: u64 = 21_004;

    let ind_ty = k.const_(monoid.ind, vec![]);
    let m = k.fvar(M_FV);
    let carrier = sel(k, monoid, CARRIER, m);
    let op = sel(k, monoid, OP, m);
    let e = sel(k, monoid, E, m);
    let ident_l = sel(k, monoid, IDENT_L, m);
    let ep = k.fvar(EP_FV);

    let hyp_ty = {
        let a = k.fvar(A_FV);
        let lhs = app2(k, op, a, ep);
        let eq = eq_of(k, lg, l1, carrier, lhs, a);
        pi_over(k, A_FV, carrier, eq)
    };
    let h = k.fvar(H_FV);

    let op_e_ep = app2(k, op, e, ep);
    let h1 = k.app(ident_l, ep); // : op e e' = e'
    let symm_h1 = symm_of(k, lg, l1, carrier, op_e_ep, ep, h1); // : e' = op e e'
    let h2 = k.app(h, e); // : op e e' = e
    let result = trans_of(k, lg, l1, carrier, ep, op_e_ep, e, symm_h1, h2, SCRATCH_FV);

    let value = lam_over(k, H_FV, hyp_ty, result);
    let value = lam_over(k, EP_FV, carrier, value);
    let value = lam_over(k, M_FV, ind_ty, value);

    let concl = eq_of(k, lg, l1, carrier, ep, e);
    let ty = pi_over(k, H_FV, hyp_ty, concl);
    let ty = pi_over(k, EP_FV, carrier, ty);
    let ty = pi_over(k, M_FV, ind_ty, ty);

    (ty, value)
}

/// `Alg.groupInvUnique : forall (G : Group) (a b c : G.carrier), G.op b a =
/// G.e -> G.op a c = G.e -> b = c`. `b = b*e = b*(a*c) = (b*a)*c = e*c = c`,
/// the shape `Nat.group_inverse_unique` uses.
#[allow(clippy::similar_names)]
fn build_group_inv_unique(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
) -> (ExprId, ExprId) {
    use structures::idx::group::{ASSOC, CARRIER, E, IDENT_L, IDENT_R, OP};
    const G_FV: u64 = 21_100;
    const A_FV: u64 = 21_101;
    const B_FV: u64 = 21_102;
    const C_FV: u64 = 21_103;
    const H1_FV: u64 = 21_104;
    const H2_FV: u64 = 21_105;
    const S1: u64 = 21_106;
    const S2: u64 = 21_107;
    const S3: u64 = 21_108;
    const S4: u64 = 21_109;

    let ind_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(G_FV);
    let carrier = sel(k, group, CARRIER, g);
    let op = sel(k, group, OP, g);
    let e = sel(k, group, E, g);
    let ident_l = sel(k, group, IDENT_L, g);
    let ident_r = sel(k, group, IDENT_R, g);
    let assoc = sel(k, group, ASSOC, g);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);

    let op_b_a = app2(k, op, b, a);
    let op_a_c = app2(k, op, a, c);
    let h1_ty = eq_of(k, lg, l1, carrier, op_b_a, e); // op b a = e
    let h2_ty = eq_of(k, lg, l1, carrier, op_a_c, e); // op a c = e
    let h1 = k.fvar(H1_FV);
    let h2 = k.fvar(H2_FV);

    // Step A: identR(b) : op b e = b ; symm -> b = op b e
    let op_b_e = app2(k, op, b, e);
    let h_a = k.app(ident_r, b);
    let symm_ha = symm_of(k, lg, l1, carrier, op_b_e, b, h_a); // b = op b e

    // Step B': congr_arg (op b .) on symm(h2) : e = op a c  =>  op b e = op b (op a c)
    let symm_h2 = symm_of(k, lg, l1, carrier, op_a_c, e, h2); // e = op a c
    let op_b_opac = app2(k, op, b, op_a_c);
    let step_b = congr_arg(k, lg, l1, carrier, e, op_a_c, symm_h2, S1, &|k2, x| {
        app2(k2, op, b, x)
    });

    let r1 = trans_of(
        k, lg, l1, carrier, b, op_b_e, op_b_opac, symm_ha, step_b, S2,
    );

    // Step C: assoc(b,a,c) : op (op b a) c = op b (op a c) ; symm.
    let op_ba_c = app2(k, op, op_b_a, c);
    let assoc_bac = {
        let e1 = k.app(assoc, b);
        let e2 = k.app(e1, a);
        k.app(e2, c)
    };
    let step_c = symm_of(k, lg, l1, carrier, op_ba_c, op_b_opac, assoc_bac);

    let r2 = trans_of(k, lg, l1, carrier, b, op_b_opac, op_ba_c, r1, step_c, S3);

    // Step D: congr_arg (. c) on h1 : op b a = e  =>  op (op b a) c = op e c
    let op_e_c = app2(k, op, e, c);
    let step_d = congr_arg(k, lg, l1, carrier, op_b_a, e, h1, S4, &|k2, x| {
        app2(k2, op, x, c)
    });

    let r3 = trans_of(k, lg, l1, carrier, b, op_ba_c, op_e_c, r2, step_d, S1);

    // Step E: identL(c) : op e c = c.
    let step_e = k.app(ident_l, c);

    let r4 = trans_of(k, lg, l1, carrier, b, op_e_c, c, r3, step_e, S2);

    let value = lam_over(k, H2_FV, h2_ty, r4);
    let value = lam_over(k, H1_FV, h1_ty, value);
    let value = lam_over(k, C_FV, carrier, value);
    let value = lam_over(k, B_FV, carrier, value);
    let value = lam_over(k, A_FV, carrier, value);
    let value = lam_over(k, G_FV, ind_ty, value);

    let concl = eq_of(k, lg, l1, carrier, b, c);
    let ty = pi_over(k, H2_FV, h2_ty, concl);
    let ty = pi_over(k, H1_FV, h1_ty, ty);
    let ty = pi_over(k, C_FV, carrier, ty);
    let ty = pi_over(k, B_FV, carrier, ty);
    let ty = pi_over(k, A_FV, carrier, ty);
    let ty = pi_over(k, G_FV, ind_ty, ty);

    (ty, value)
}

/// `Alg.ringMulZero : forall (R : Ring) (a : R.carrier), R.mul a R.zero =
/// R.zero`, from the additive-group + distributive axioms alone -- no
/// multiplicative identity is ever used.
#[allow(clippy::too_many_lines)]
fn build_ring_mul_zero(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    ring: &RecordNames,
) -> (ExprId, ExprId) {
    use structures::idx::ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, MUL, NEG, NEG_ADD, ZERO,
    };
    const R_FV: u64 = 21_200;
    const A_FV: u64 = 21_201;
    const S1: u64 = 21_202;
    const S2: u64 = 21_203;
    const S3: u64 = 21_204;
    const S4: u64 = 21_205;

    let ind_ty = k.const_(ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let zero = sel(k, ring, ZERO, r);
    let add = sel(k, ring, ADD, r);
    let mul = sel(k, ring, MUL, r);
    let add_assoc = sel(k, ring, ADD_ASSOC, r);
    let add_comm = sel(k, ring, ADD_COMM, r);
    let add_zero = sel(k, ring, ADD_ZERO, r);
    let distrib_l = sel(k, ring, DISTRIB_L, r);
    let neg = sel(k, ring, NEG, r);
    let neg_add = sel(k, ring, NEG_ADD, r);

    let a = k.fvar(A_FV);
    let x = app2(k, mul, a, zero); // x := mul a zero

    // EQ1 : zero = add zero zero  (symm of addZero at zero)
    let add_zero_zero = app2(k, add, zero, zero);
    let addzero_at_zero = k.app(add_zero, zero); // : add zero zero = zero
    let eq1 = symm_of(k, lg, l1, carrier, add_zero_zero, zero, addzero_at_zero);

    // EQ2 : x = mul a (add zero zero)   (congr via EQ1, f y = mul a y)
    let mul_a_addzz = app2(k, mul, a, add_zero_zero);
    let eq2 = congr_arg(
        k,
        lg,
        l1,
        carrier,
        zero,
        add_zero_zero,
        eq1,
        S1,
        &|k2, y| app2(k2, mul, a, y),
    );

    // EQ3 : mul a (add zero zero) = add x x   (distribL a zero zero)
    let add_x_x = app2(k, add, x, x);
    let eq3 = {
        let e1 = k.app(distrib_l, a);
        let e2 = k.app(e1, zero);
        k.app(e2, zero)
    };

    let xeq = trans_of(k, lg, l1, carrier, x, mul_a_addzz, add_x_x, eq2, eq3, S2); // x = add x x

    // negAddL(x) : add (neg x) x = zero, derived from addComm + negAdd.
    let neg_x = k.app(neg, x);
    let add_negx_x = app2(k, add, neg_x, x);
    let add_x_negx = app2(k, add, x, neg_x);
    let comm_negx_x = {
        let e1 = k.app(add_comm, neg_x);
        k.app(e1, x)
    }; // : add (neg x) x = add x (neg x)
    let negadd_x = k.app(neg_add, x); // : add x (neg x) = zero
    let neg_add_l = trans_of(
        k,
        lg,
        l1,
        carrier,
        add_negx_x,
        add_x_negx,
        zero,
        comm_negx_x,
        negadd_x,
        S3,
    );

    // R2 : zero = add (neg x) (add x x), via symm(neg_add_l) then congr on xeq.
    let eq5 = symm_of(k, lg, l1, carrier, add_negx_x, zero, neg_add_l); // zero = add(neg x)x
    let add_negx_addxx = app2(k, add, neg_x, add_x_x);
    let eq6 = congr_arg(k, lg, l1, carrier, x, add_x_x, xeq, S4, &|k2, y| {
        app2(k2, add, neg_x, y)
    });
    let r2 = trans_of(
        k,
        lg,
        l1,
        carrier,
        zero,
        add_negx_x,
        add_negx_addxx,
        eq5,
        eq6,
        S1,
    );

    // R3 : zero = add (add (neg x) x) x, via symm(addAssoc(neg x, x, x)).
    let add_addnegxx_x = app2(k, add, add_negx_x, x);
    let assoc_nxx = {
        let e1 = k.app(add_assoc, neg_x);
        let e2 = k.app(e1, x);
        k.app(e2, x)
    }; // : add (add (neg x) x) x = add (neg x) (add x x)
    let eq7 = symm_of(
        k,
        lg,
        l1,
        carrier,
        add_addnegxx_x,
        add_negx_addxx,
        assoc_nxx,
    );
    let r3 = trans_of(
        k,
        lg,
        l1,
        carrier,
        zero,
        add_negx_addxx,
        add_addnegxx_x,
        r2,
        eq7,
        S2,
    );

    // R4 : zero = add zero x, via congr on negAddL : add(neg x)x = zero.
    let add_zero_x = app2(k, add, zero, x);
    let eq8 = congr_arg(
        k,
        lg,
        l1,
        carrier,
        add_negx_x,
        zero,
        neg_add_l,
        S3,
        &|k2, y| app2(k2, add, y, x),
    );
    let r4 = trans_of(
        k,
        lg,
        l1,
        carrier,
        zero,
        add_addnegxx_x,
        add_zero_x,
        r3,
        eq8,
        S4,
    );

    // EQ9 : add zero x = x  (addZero-left, derived from addComm + addZero).
    let comm_zero_x = {
        let e1 = k.app(add_comm, zero);
        k.app(e1, x)
    }; // : add zero x = add x zero
    let add_zero_at_x = k.app(add_zero, x); // : add x zero = x
    let add_x_zero = app2(k, add, x, zero);
    let eq9 = trans_of(
        k,
        lg,
        l1,
        carrier,
        add_zero_x,
        add_x_zero,
        x,
        comm_zero_x,
        add_zero_at_x,
        S1,
    );

    let r5 = trans_of(k, lg, l1, carrier, zero, add_zero_x, x, r4, eq9, S2); // zero = x
    let result = symm_of(k, lg, l1, carrier, zero, x, r5); // x = zero

    let value = lam_over(k, A_FV, carrier, result);
    let value = lam_over(k, R_FV, ind_ty, value);

    let concl = eq_of(k, lg, l1, carrier, x, zero);
    let ty = pi_over(k, A_FV, carrier, concl);
    let ty = pi_over(k, R_FV, ind_ty, ty);

    (ty, value)
}

// ---------------------------------------------------------------------------
// The payoff: `det_one` over an arbitrary `Alg.CommRing`.
// ---------------------------------------------------------------------------

/// `Alg.sumR : Pi (R : CommRing), (Nat -> R.carrier) -> Nat -> R.carrier`,
/// `Nat.rec` with a CONSTANT motive `fun _ => R.carrier` (`f` is closed over
/// in the surrounding lambda, so it never varies across the recursion --
/// unlike `detR` below, which needs a different matrix at each step).
fn build_sum_r(
    k: &mut Kernel,
    l1: LevelId,
    comm_ring: &RecordNames,
    nat_rec: NameId,
    nat_ty: ExprId,
) -> (ExprId, ExprId) {
    use structures::idx::comm_ring::{ADD, CARRIER, ZERO};
    const R_FV: u64 = 21_300;
    const F_FV: u64 = 21_301;
    const N_FV: u64 = 21_302;
    const NP_FV: u64 = 21_303;
    const IH_FV: u64 = 21_304;
    let anon = k.anon();

    let ind_ty = k.const_(comm_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, comm_ring, CARRIER, r);
    let zero = sel(k, comm_ring, ZERO, r);
    let add = sel(k, comm_ring, ADD, r);
    let f_ty = arrow(k, nat_ty, carrier);
    let f = k.fvar(F_FV);

    let motive = k.lam(anon, nat_ty, carrier, BinderInfo::Default);
    let step = {
        let np = k.fvar(NP_FV);
        let ih = k.fvar(IH_FV);
        let f_np = k.app(f, np);
        let body = app2(k, add, ih, f_np);
        let inner = lam_over(k, IH_FV, carrier, body);
        lam_over(k, NP_FV, nat_ty, inner)
    };
    let rec_c = k.const_(nat_rec, vec![l1]);
    let rec_applied = {
        let e = k.app(rec_c, motive);
        let e = k.app(e, zero);
        k.app(e, step)
    }; // : Nat -> R.carrier

    let n = k.fvar(N_FV);
    let result = k.app(rec_applied, n);
    let value = lam_over(k, N_FV, nat_ty, result);
    let value = lam_over(k, F_FV, f_ty, value);
    let value = lam_over(k, R_FV, ind_ty, value);

    let inner_ty = arrow(k, nat_ty, carrier);
    let f_to_result = arrow(k, f_ty, inner_ty);
    let ty = pi_over(k, R_FV, ind_ty, f_to_result);

    (ty, value)
}

/// `Alg.altSignR : Pi (R : CommRing), Nat -> R.carrier`,
/// `altSignR R 0 = R.one`, `altSignR R (succ n) = R.neg (altSignR R n)`.
fn build_alt_sign_r(
    k: &mut Kernel,
    l1: LevelId,
    comm_ring: &RecordNames,
    nat_rec: NameId,
    nat_ty: ExprId,
) -> (ExprId, ExprId) {
    use structures::idx::comm_ring::{CARRIER, NEG, ONE};
    const R_FV: u64 = 21_310;
    const N_FV: u64 = 21_311;
    const NP_FV: u64 = 21_312;
    const IH_FV: u64 = 21_313;
    let anon = k.anon();

    let ind_ty = k.const_(comm_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, comm_ring, CARRIER, r);
    let one = sel(k, comm_ring, ONE, r);
    let neg = sel(k, comm_ring, NEG, r);

    let motive = k.lam(anon, nat_ty, carrier, BinderInfo::Default);
    let step = {
        let ih = k.fvar(IH_FV);
        let body = k.app(neg, ih);
        let inner = lam_over(k, IH_FV, carrier, body);
        lam_over(k, NP_FV, nat_ty, inner)
    };
    let rec_c = k.const_(nat_rec, vec![l1]);
    let rec_applied = {
        let e = k.app(rec_c, motive);
        let e = k.app(e, one);
        k.app(e, step)
    };
    let n = k.fvar(N_FV);
    let result = k.app(rec_applied, n);
    let value = lam_over(k, N_FV, nat_ty, result);
    let value = lam_over(k, R_FV, ind_ty, value);

    let ty = {
        let t = arrow(k, nat_ty, carrier);
        pi_over(k, R_FV, ind_ty, t)
    };
    (ty, value)
}

/// `Alg.detR : Pi (R : CommRing), Nat -> (Nat -> Nat -> R.carrier) ->
/// R.carrier`, `detR R 0 A = R.one`, `detR R (succ m) A = sumR R (fun j =>
/// R.mul (altSignR R j) (R.mul (A 0 j) (detR R m (matMinor A 0 j)))) (succ
/// m)`. `Nat.rec`'s motive is FUNCTION-TYPED, `(Nat->Nat->R.carrier) ->
/// R.carrier`, because the recursive call is at a DIFFERENT matrix (the
/// minor) -- the same device `Rat.det`'s own module doc names.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn build_det_r(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    comm_ring: &RecordNames,
    nat_rec: NameId,
    nat_ty: ExprId,
    nat_zero: ExprId,
    nat_succ: NameId,
    mat_skip: NameId,
    sum_r: NameId,
    alt_sign_r: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::comm_ring::{CARRIER, MUL, ONE};
    const R_FV: u64 = 21_320;
    const M_FV: u64 = 21_321;
    const A_FV: u64 = 21_322;
    const MP_FV: u64 = 21_323; // m' (predecessor)
    const IH_FV: u64 = 21_324; // recursive call, function-typed
    const AA_FV: u64 = 21_325; // the A bound inside base/step (function arg)
    const J_FV: u64 = 21_326;
    const ROW_FV: u64 = 21_327;
    const COL_FV: u64 = 21_328;
    let _ = lg;
    let anon = k.anon();

    let ind_ty = k.const_(comm_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, comm_ring, CARRIER, r);
    let one = sel(k, comm_ring, ONE, r);
    let mul = sel(k, comm_ring, MUL, r);

    let mat_ty = {
        let row_ty = arrow(k, nat_ty, carrier);
        arrow(k, nat_ty, row_ty)
    }; // Nat -> Nat -> R.carrier
    let ih_ty = arrow(k, mat_ty, carrier); // (Nat->Nat->R.carrier) -> R.carrier

    // motive : Nat -> Sort 1, constant = ih_ty
    let motive = k.lam(anon, nat_ty, ih_ty, BinderInfo::Default);

    // base : fun (A : mat_ty) => R.one
    let base = {
        let body = one;
        lam_over(k, AA_FV, mat_ty, body)
    };

    // matMinor A i j := fun r c => A (matSkip i r) (matSkip j c), specialized
    // here to i = 0, j specific.
    let mat_minor_0_j = |k2: &mut Kernel, a_expr: ExprId, j: ExprId| -> ExprId {
        let row = k2.fvar(ROW_FV);
        let col = k2.fvar(COL_FV);
        let skip_fn = k2.const_(mat_skip, vec![]);
        let zero0 = nat_zero;
        let skip_row = {
            let e = k2.app(skip_fn, zero0);
            k2.app(e, row)
        }; // matSkip 0 row
        let skip_col = {
            let e = k2.app(skip_fn, j);
            k2.app(e, col)
        }; // matSkip j col
        let applied = {
            let e = k2.app(a_expr, skip_row);
            k2.app(e, skip_col)
        };
        let inner = lam_over(k2, COL_FV, nat_ty, applied);
        lam_over(k2, ROW_FV, nat_ty, inner)
    };

    // step : fun (m' : Nat) (ih : mat_ty -> R.carrier) (A : mat_ty) =>
    //   sumR R (fun j => mul (altSignR R j) (mul (A 0 j) (ih (matMinor A 0 j)))) (succ m')
    let step = {
        let ih = k.fvar(IH_FV);
        let aa = k.fvar(AA_FV);
        let summand = {
            let j = k.fvar(J_FV);
            let alt_j = {
                let c = k.const_(alt_sign_r, vec![]);
                let e = k.app(c, r);
                k.app(e, j)
            };
            let a_0_j = {
                let zero0 = nat_zero;
                let e = k.app(aa, zero0);
                k.app(e, j)
            };
            let minor = mat_minor_0_j(k, aa, j);
            let ih_minor = k.app(ih, minor);
            let inner_mul = app2(k, mul, a_0_j, ih_minor);
            let outer_mul = app2(k, mul, alt_j, inner_mul);
            lam_over(k, J_FV, nat_ty, outer_mul)
        };
        let mp = k.fvar(MP_FV);
        let succ_mp = {
            let c = k.const_(nat_succ, vec![]);
            k.app(c, mp)
        };
        let sum_c = k.const_(sum_r, vec![]);
        let body = {
            let e = k.app(sum_c, r);
            let e = k.app(e, summand);
            k.app(e, succ_mp)
        };
        let with_aa = lam_over(k, AA_FV, mat_ty, body);
        let with_ih = lam_over(k, IH_FV, ih_ty, with_aa);
        lam_over(k, MP_FV, nat_ty, with_ih)
    };

    let rec_c = k.const_(nat_rec, vec![l1]);
    let rec_applied = {
        let e = k.app(rec_c, motive);
        let e = k.app(e, base);
        k.app(e, step)
    }; // : Nat -> (mat_ty -> R.carrier)

    let m = k.fvar(M_FV);
    let after_m = k.app(rec_applied, m); // : mat_ty -> R.carrier
    let a = k.fvar(A_FV);
    let result = k.app(after_m, a);

    let value = lam_over(k, A_FV, mat_ty, result);
    let value = lam_over(k, M_FV, nat_ty, value);
    let value = lam_over(k, R_FV, ind_ty, value);

    let ty = {
        let t = arrow(k, mat_ty, carrier);
        let t = arrow(k, nat_ty, t);
        pi_over(k, R_FV, ind_ty, t)
    };

    (ty, value)
}

/// `Alg.commRingDetOne : forall (R : CommRing) (A : Nat -> Nat -> R.carrier),
/// detR R 1 A = A 0 0`. `detR R 1 A` iota/beta-reduces to `add R.zero (mul
/// R.one (mul (A 0 0) R.one))` with NO law needed (both `detR`'s and
/// `sumR`'s base cases fire, and `altSignR R 0` reduces to `R.one`) -- the
/// proof below is stated about that reduced form and accepted because the
/// kernel's `def_eq` bridges it back to `detR R 1 A` during
/// `add_declaration`. `det_mul`/multiplicativity is explicitly NOT attempted
/// (ADR-1578).
#[allow(clippy::too_many_arguments)]
fn build_comm_ring_det_one(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    comm_ring: &RecordNames,
    nat_ty: ExprId,
    nat_zero: ExprId,
    nat_succ: NameId,
    det_r: NameId,
) -> (ExprId, ExprId) {
    use structures::idx::comm_ring::{
        ADD, ADD_COMM, ADD_ZERO, CARRIER, MUL, MUL_ONE_L, MUL_ONE_R, ONE, ZERO,
    };
    const R_FV: u64 = 21_400;
    const A_FV: u64 = 21_401;
    const AZ_A_FV: u64 = 21_402;
    const AZ_SCRATCH_FV: u64 = 21_403;
    const S1: u64 = 21_404;

    let ind_ty = k.const_(comm_ring.ind, vec![]);
    let r = k.fvar(R_FV);
    let carrier = sel(k, comm_ring, CARRIER, r);
    let zero = sel(k, comm_ring, ZERO, r);
    let one = sel(k, comm_ring, ONE, r);
    let add = sel(k, comm_ring, ADD, r);
    let mul = sel(k, comm_ring, MUL, r);
    let add_comm = sel(k, comm_ring, ADD_COMM, r);
    let add_zero = sel(k, comm_ring, ADD_ZERO, r);
    let mul_one_l = sel(k, comm_ring, MUL_ONE_L, r);
    let mul_one_r = sel(k, comm_ring, MUL_ONE_R, r);

    let mat_ty = {
        let row_ty = arrow(k, nat_ty, carrier);
        arrow(k, nat_ty, row_ty)
    };
    let a = k.fvar(A_FV);
    let a00 = {
        let e = k.app(a, nat_zero);
        k.app(e, nat_zero)
    };

    let mul_a00_one = app2(k, mul, a00, one);
    let y = app2(k, mul, one, mul_a00_one); // one * (A00 * one)

    // Step1: mulOneR : mul A00 one = A00.
    let step1 = k.app(mul_one_r, a00);
    // Step2: congr (mul one .) on step1 : y = mul one A00.
    let mul_one_a00 = app2(k, mul, one, a00);
    let step2 = congr_arg(k, lg, l1, carrier, mul_a00_one, a00, step1, S1, &|k2, w| {
        app2(k2, mul, one, w)
    });
    // Step3: mulOneL : mul one A00 = A00.
    let step3 = k.app(mul_one_l, a00);
    let y_eq_a00 = trans_of(k, lg, l1, carrier, y, mul_one_a00, a00, step2, step3, S1);

    // Step5: addZeroL (generic, applied at y) : add zero y = y.
    let add_zero_left = derive_left_unit(
        k,
        lg,
        l1,
        carrier,
        add,
        zero,
        add_comm,
        add_zero,
        AZ_A_FV,
        AZ_SCRATCH_FV,
    );
    let step5 = k.app(add_zero_left, y); // : add zero y = y

    let add_zero_y = app2(k, add, zero, y);
    let result = trans_of(k, lg, l1, carrier, add_zero_y, y, a00, step5, y_eq_a00, S1);

    let value = lam_over(k, A_FV, mat_ty, result);
    let value = lam_over(k, R_FV, ind_ty, value);

    let one_n = {
        let c = k.const_(nat_succ, vec![]);
        k.app(c, nat_zero)
    };
    let det_r_c = k.const_(det_r, vec![]);
    let det_r_1_a = {
        let e = k.app(det_r_c, r);
        let e = k.app(e, one_n);
        k.app(e, a)
    };
    let concl = eq_of(k, lg, l1, carrier, det_r_1_a, a00);
    let ty = pi_over(k, A_FV, mat_ty, concl);
    let ty = pi_over(k, R_FV, ind_ty, ty);

    (ty, value)
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

/// Every ADR-1578 name this module declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AlgebraNames {
    pub nat_comm_add_monoid: NameId,
    pub rat_comm_mul_monoid: NameId,
    pub int_add_group: NameId,
    pub rat_add_group: NameId,
    pub int_ring: NameId,
    pub rat_ring: NameId,
    pub int_comm_ring: NameId,
    pub rat_comm_ring: NameId,
    pub rat_field: NameId,
    pub monoid_ident_unique: NameId,
    pub group_inv_unique: NameId,
    pub ring_mul_zero: NameId,
    pub sum_r: NameId,
    pub alt_sign_r: NameId,
    pub det_r: NameId,
    pub comm_ring_det_one: NameId,
}

pub(crate) fn intern_algebra_instances(k: &mut Kernel) -> AlgebraNames {
    let alg = alg_root(k);
    AlgebraNames {
        nat_comm_add_monoid: {
            let root = k.name_str(alg, "Nat");
            k.name_str(root, "commAddMonoid")
        },
        rat_comm_mul_monoid: {
            let root = k.name_str(alg, "Rat");
            k.name_str(root, "commMulMonoid")
        },
        int_add_group: {
            let root = k.name_str(alg, "Int");
            k.name_str(root, "addGroup")
        },
        rat_add_group: {
            let root = k.name_str(alg, "Rat");
            k.name_str(root, "addGroup")
        },
        int_ring: {
            let root = k.name_str(alg, "Int");
            k.name_str(root, "ring")
        },
        rat_ring: {
            let root = k.name_str(alg, "Rat");
            k.name_str(root, "ring")
        },
        int_comm_ring: {
            let root = k.name_str(alg, "Int");
            k.name_str(root, "commRing")
        },
        rat_comm_ring: {
            let root = k.name_str(alg, "Rat");
            k.name_str(root, "commRing")
        },
        rat_field: {
            let root = k.name_str(alg, "Rat");
            k.name_str(root, "field")
        },
        monoid_ident_unique: k.name_str(alg, "monoidIdentUnique"),
        group_inv_unique: k.name_str(alg, "groupInvUnique"),
        ring_mul_zero: k.name_str(alg, "ringMulZero"),
        sum_r: k.name_str(alg, "sumR"),
        alt_sign_r: k.name_str(alg, "altSignR"),
        det_r: k.name_str(alg, "detR"),
        comm_ring_det_one: k.name_str(alg, "commRingDetOne"),
    }
}

pub(crate) fn declare_algebra_instances_all(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: &RatPrelude,
    st: &structures::StructuresNames,
    names: &AlgebraNames,
) -> Result<(), KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    declare_instances(k, lg, l1, p, st, names)?;

    {
        let (ty, value) = build_monoid_ident_unique(k, lg, l1, &st.monoid);
        k.add_declaration(Declaration::Theorem {
            name: names.monoid_ident_unique,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_group_inv_unique(k, lg, l1, &st.group);
        k.add_declaration(Declaration::Theorem {
            name: names.group_inv_unique,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    {
        let (ty, value) = build_ring_mul_zero(k, lg, l1, &st.ring);
        k.add_declaration(Declaration::Theorem {
            name: names.ring_mul_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    let nat_ty = k.const_(p.int.nat.nat, vec![]);
    let nat_zero = k.const_(p.int.nat.zero, vec![]);
    let nat_succ = p.int.nat.succ;
    let nat_rec = p.int.nat.rec;

    {
        let (ty, value) = build_sum_r(k, l1, &st.comm_ring, nat_rec, nat_ty);
        k.add_declaration(Declaration::Definition {
            name: names.sum_r,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    {
        let (ty, value) = build_alt_sign_r(k, l1, &st.comm_ring, nat_rec, nat_ty);
        k.add_declaration(Declaration::Definition {
            name: names.alt_sign_r,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    {
        let (ty, value) = build_det_r(
            k,
            lg,
            l1,
            &st.comm_ring,
            nat_rec,
            nat_ty,
            nat_zero,
            nat_succ,
            p.mat_skip,
            names.sum_r,
            names.alt_sign_r,
        );
        k.add_declaration(Declaration::Definition {
            name: names.det_r,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    {
        let (ty, value) = build_comm_ring_det_one(
            k,
            lg,
            l1,
            &st.comm_ring,
            nat_ty,
            nat_zero,
            nat_succ,
            names.det_r,
        );
        k.add_declaration(Declaration::Theorem {
            name: names.comm_ring_det_one,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

#[cfg(test)]
mod algebra_instances_tests {
    use super::*;
    use crate::build_rat_prelude;

    /// `Alg.monoidIdentUnique` applied at TWO CONCRETE carriers with fully
    /// concrete numeral witnesses and existing lemma names as the hypothesis
    /// -- the "instantiate concretely" half of
    /// `docs/contributor-guide/kernel-proof-engineering.md`'s discipline.
    /// `M` is typed `Alg.Monoid`, not `Alg.CommMonoid` -- no inheritance, so
    /// the theorem needs a genuine `Monoid` value; built here inline from the
    /// SAME underlying lemma constants the `CommMonoid` instances use (one
    /// fewer field, `comm` dropped).
    #[test]
    fn monoid_ident_unique_applies_concretely_at_nat_add_and_rat_mul() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = p.int.nat;
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let thm = k.const_(p.algebra.monoid_ident_unique, vec![]);

        // Nat: M := (Nat, add, 0) as a Monoid, e' := 0, h := Nat.add_zero.
        let m = {
            use structures::idx::monoid::{ASSOC, CARRIER, E, IDENT_L, IDENT_R, OP};
            let nat_ty = k.const_(np.nat, vec![]);
            let add = k.const_(np.add, vec![]);
            let zero = k.const_(np.zero, vec![]);
            let assoc = k.const_(np.add_assoc, vec![]);
            let ident_l = k.const_(np.zero_add, vec![]);
            let ident_r = k.const_(np.add_zero, vec![]);
            let mut args = vec![ExprId(0); IDENT_R + 1];
            args[CARRIER] = nat_ty;
            args[OP] = add;
            args[E] = zero;
            args[ASSOC] = assoc;
            args[IDENT_L] = ident_l;
            args[IDENT_R] = ident_r;
            mk_instance(&mut k, &p.int.nat.structures.monoid, &args)
        };
        let zero = k.const_(np.zero, vec![]);
        let h = k.const_(np.add_zero, vec![]);
        let applied = {
            let e1 = k.app(thm, m);
            let e2 = k.app(e1, zero);
            k.app(e2, h)
        };
        let ty = k.infer(applied).expect("nat instantiation must type-check");
        let nat_ty = k.const_(np.nat, vec![]);
        let expect = eq_of(&mut k, &np.logic, l1, nat_ty, zero, zero);
        assert!(
            k.def_eq(ty, expect),
            "nat instantiation's type must be Eq Nat 0 0"
        );

        // Rat: M := (Rat, mul, 1) as a Monoid, e' := 1, h := Rat.mul_one.
        let m2 = {
            use structures::idx::monoid::{ASSOC, CARRIER, E, IDENT_L, IDENT_R, OP};
            let rat_ty = k.const_(p.int.rat, vec![]);
            let mul = k.const_(p.int.rat_mul, vec![]);
            let one = k.const_(p.one, vec![]);
            let assoc = k.const_(p.mul_assoc, vec![]);
            let comm = k.const_(p.mul_comm, vec![]);
            let mul_one = k.const_(p.mul_one, vec![]);
            let ident_l = derive_left_unit(
                &mut k, &np.logic, l1, rat_ty, mul, one, comm, mul_one, 20_010, 20_011,
            );
            let mut args = vec![ExprId(0); IDENT_R + 1];
            args[CARRIER] = rat_ty;
            args[OP] = mul;
            args[E] = one;
            args[ASSOC] = assoc;
            args[IDENT_L] = ident_l;
            args[IDENT_R] = mul_one;
            mk_instance(&mut k, &p.int.nat.structures.monoid, &args)
        };
        let one = k.const_(p.one, vec![]);
        let h2 = k.const_(p.mul_one, vec![]);
        let applied2 = {
            let e1 = k.app(thm, m2);
            let e2 = k.app(e1, one);
            k.app(e2, h2)
        };
        let ty2 = k
            .infer(applied2)
            .expect("rat instantiation must type-check");
        let rat_ty = k.const_(p.int.rat, vec![]);
        let expect2 = eq_of(&mut k, &np.logic, l1, rat_ty, one, one);
        assert!(
            k.def_eq(ty2, expect2),
            "rat instantiation's type must be Eq Rat 1 1"
        );
    }

    /// `Alg.groupInvUnique` applied at TWO CONCRETE carriers (Int, Rat),
    /// closed over symbolic elements `a b c` (`fun a b c => thm G a b c`) so
    /// the check needs no `LocalContext` -- confirms the generic theorem
    /// specializes and type-checks through each instance's selectors.
    #[test]
    fn group_inv_unique_applies_at_int_and_rat_instances() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");

        for (g_name, carrier_const, label) in [
            (p.algebra.int_add_group, p.int.z, "Int"),
            (p.algebra.rat_add_group, p.int.rat, "Rat"),
        ] {
            const A_FV: u64 = 30_000;
            const B_FV: u64 = 30_001;
            const C_FV: u64 = 30_002;
            let thm = k.const_(p.algebra.group_inv_unique, vec![]);
            let g = k.const_(g_name, vec![]);
            let carrier = k.const_(carrier_const, vec![]);
            let closed = {
                let a = k.fvar(A_FV);
                let b = k.fvar(B_FV);
                let c = k.fvar(C_FV);
                let applied = {
                    let e1 = k.app(thm, g);
                    let e2 = k.app(e1, a);
                    let e3 = k.app(e2, b);
                    k.app(e3, c)
                };
                let v = lam_over(&mut k, C_FV, carrier, applied);
                let v = lam_over(&mut k, B_FV, carrier, v);
                lam_over(&mut k, A_FV, carrier, v)
            };
            k.infer(closed)
                .unwrap_or_else(|e| panic!("{label} instantiation must type-check: {e:?}"));
        }
    }

    /// `Alg.ringMulZero` applied at TWO CONCRETE carriers (Int, Rat), closed
    /// over a symbolic `a`, and its type compared (also closed) against
    /// `mul a zero = zero` with `mul`/`zero` iota-reduced through the
    /// instance's own selectors.
    #[test]
    fn ring_mul_zero_applies_at_int_and_rat_instances() {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);

        for (r_name, carrier_const, label) in [
            (p.algebra.int_ring, p.int.z, "Int"),
            (p.algebra.rat_ring, p.int.rat, "Rat"),
        ] {
            use structures::idx::ring::{MUL, ZERO};
            const A_FV: u64 = 30_100;
            let thm = k.const_(p.algebra.ring_mul_zero, vec![]);
            let r = k.const_(r_name, vec![]);
            let carrier = k.const_(carrier_const, vec![]);
            let closed_value = {
                let a = k.fvar(A_FV);
                let applied = {
                    let e1 = k.app(thm, r);
                    k.app(e1, a)
                };
                lam_over(&mut k, A_FV, carrier, applied)
            };
            let ty = k
                .infer(closed_value)
                .unwrap_or_else(|e| panic!("{label} instantiation must type-check: {e:?}"));

            let closed_expected_ty = {
                let a = k.fvar(A_FV);
                let mul = sel(&mut k, &p.int.nat.structures.ring, MUL, r);
                let zero = sel(&mut k, &p.int.nat.structures.ring, ZERO, r);
                let mul_a_zero = app2(&mut k, mul, a, zero);
                let eq = eq_of(&mut k, &p.int.nat.logic, l1, carrier, mul_a_zero, zero);
                pi_over(&mut k, A_FV, carrier, eq)
            };
            assert!(
                k.def_eq(ty, closed_expected_ty),
                "{label}: mul a zero = zero"
            );
        }
    }

    /// THE PAYOFF TEST (ADR-1578). `Alg.commRingDetOne` instantiated at
    /// `Rat.commRing` type-checks (closed over a symbolic matrix `A`);
    /// separately, whether `detR Rat.commRing 1 A` is `def_eq` to
    /// `Rat.det A 1` SYMBOLICALLY is measured and reported here rather than
    /// assumed -- `detR` and `Rat.det` are two independently-built
    /// `Nat.rec` instances (the `Nat.multichoose` boundary
    /// `docs/contributor-guide/kernel-proof-engineering.md` names), so this
    /// is exactly the case where "computes the same value" and "is the same
    /// term" can come apart. Compared as `fun A => detR ... A` versus
    /// `fun A => Rat.det A ...`, both closed over the SAME bound `A_FV`, so
    /// no `LocalContext` is needed.
    #[test]
    fn comm_ring_det_one_instantiates_at_rat_and_the_agreement_with_rat_det_is_measured() {
        const A_FV: u64 = 30_200;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let thm = k.const_(p.algebra.comm_ring_det_one, vec![]);
        let r = k.const_(p.algebra.rat_comm_ring, vec![]);

        let nat_ty = k.const_(p.int.nat.nat, vec![]);
        let rat_ty = k.const_(p.int.rat, vec![]);
        let mat_ty = {
            let row_ty = arrow(&mut k, nat_ty, rat_ty);
            arrow(&mut k, nat_ty, row_ty)
        };
        let one_n = {
            let c = k.const_(p.int.nat.succ, vec![]);
            let zero_n = k.const_(p.int.nat.zero, vec![]);
            k.app(c, zero_n)
        };

        let closed_applied = {
            let a = k.fvar(A_FV);
            let applied = {
                let e1 = k.app(thm, r);
                k.app(e1, a)
            };
            lam_over(&mut k, A_FV, mat_ty, applied)
        };
        k.infer(closed_applied)
            .expect("Rat instantiation of commRingDetOne must type-check");

        // Measure: is `detR R 1 A` def_eq to `Rat.det A 1` at a SYMBOLIC A?
        let closed_det_r = {
            let a = k.fvar(A_FV);
            let c = k.const_(p.algebra.det_r, vec![]);
            let e1 = k.app(c, r);
            let e2 = k.app(e1, one_n);
            let v = k.app(e2, a);
            lam_over(&mut k, A_FV, mat_ty, v)
        };
        let closed_rat_det = {
            let a = k.fvar(A_FV);
            let c = k.const_(p.det, vec![]);
            let e1 = k.app(c, a);
            let v = k.app(e1, one_n);
            lam_over(&mut k, A_FV, mat_ty, v)
        };
        let agree = k.def_eq(closed_det_r, closed_rat_det);
        println!(
            "ADR-1578 payoff measurement: detR(Rat.commRing, 1, A) def_eq Rat.det(A, 1) at a symbolic A = {agree}"
        );
        // Not asserted either way -- this is the measurement the ADR's
        // Evidence section reports, not a pass/fail gate.
    }
}
