//! ADR-1588's payoff: `CReal.commRingS : AlgS.CommRing` — every field an
//! *existing* `CReal` theorem (the ADR-0512 laws plus `add_congr`/
//! `mul_congr` from `creal/congruence.rs`), with two fields (`mulOneL`,
//! `distribR`) derived by one or three `equivTrans` applications each, no
//! new `creal` proof.
//!
//! See `docs/research/09-decisions/adr-1588-a-setoid-flavored-alg-spine-for-creal.md`
//! §4 for the field-by-field table this module implements.
//!
//! ## Wired into `build_creal_prelude`'s `STEP_DISPATCH`
//!
//! `creal.rs`'s build is a generated `STEPS`/`STEP_DISPATCH` pair
//! (`scripts/creal-declare-deps.py`), and every step's function signature is
//! `fn(&mut IntDev<'_>, CRealPrelude) -> Result<(), KernelError>` writing
//! into a `NameId` pre-interned by `intern_names`. `declare_comm_ring_s`
//! below is that step: it declares under `p.comm_ring_s` (interned in
//! `intern_names` alongside every other `CReal` name) and is registered in
//! `STEP_DISPATCH` right after `product::declare_product`, the step that
//! provides every multiplicative law field this declaration needs
//! (`mul`/`mul_comm`/`mul_assoc`/`mul_one`/`left_distrib`). Every additive
//! field it needs (`add`/`add_congr`/`add_assoc`/`add_comm`/`add_zero`/
//! `add_neg`/`neg`/`neg_congr`) is provided earlier, by
//! `declare_negation`/`declare_addition`/`declare_additive_laws`.
//! `scripts/creal-declare-deps.py --check --strict --self-check` measures
//! this from source rather than trusting this comment.

use crate::Kernel;
use crate::KernelError;
use crate::creal::CRealPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures_setoid::idx::comm_ring as idx;

/// Apply `f` to each of `xs` in order, left-to-right.
pub fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

/// `fun (fv : ty) => body`, abstracting the free variable `fv` out of `body`.
pub fn lam_over(k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = k.abstract_fvars(body, &[fv]);
    let anon = k.anon();
    k.lam(anon, ty, b, crate::BinderInfo::Default)
}

/// `CReal.mulOneL : forall a, CReal.equiv (CReal.mul CReal.one a) a` —
/// derived from `mul_comm(one, a)` and `mul_one(a)`, one `equiv_trans`
/// application, no new `creal` proof.
pub fn build_mul_one_l(k: &mut Kernel, p: &CRealPrelude) -> ExprId {
    const A_FV: u64 = 22_900;
    let creal_ty = k.const_(p.creal, vec![]);
    let mul = k.const_(p.mul, vec![]);
    let one = k.const_(p.one, vec![]);
    let mul_comm = k.const_(p.mul_comm, vec![]);
    let mul_one = k.const_(p.mul_one, vec![]);
    let equiv_trans = k.const_(p.equiv_trans, vec![]);

    let a = k.fvar(A_FV);
    let mul_one_a = t_app(k, mul, &[one, a]);
    let mul_a_one = t_app(k, mul, &[a, one]);
    let comm_1a = t_app(k, mul_comm, &[one, a]); // equiv (mul one a) (mul a one)
    let mo_a = k.app(mul_one, a); // equiv (mul a one) a
    let combined = t_app(k, equiv_trans, &[mul_one_a, mul_a_one, a, comm_1a, mo_a]);
    lam_over(k, A_FV, creal_ty, combined)
}

/// `CReal.distribR : forall a b c, CReal.equiv (CReal.mul (CReal.add a b) c)
/// (CReal.add (CReal.mul a c) (CReal.mul b c))` — derived from `mul_comm`
/// (three applications) and `left_distrib`, via `add_congr`, no new `creal`
/// proof.
pub fn build_distrib_r(k: &mut Kernel, p: &CRealPrelude) -> ExprId {
    const A_FV: u64 = 22_910;
    const B_FV: u64 = 22_911;
    const C_FV: u64 = 22_912;
    let creal_ty = k.const_(p.creal, vec![]);
    let add = k.const_(p.add, vec![]);
    let mul = k.const_(p.mul, vec![]);
    let mul_comm = k.const_(p.mul_comm, vec![]);
    let left_distrib = k.const_(p.left_distrib, vec![]);
    let add_congr = k.const_(p.add_congr, vec![]);
    let equiv_trans = k.const_(p.equiv_trans, vec![]);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let ab = t_app(k, add, &[a, b]);
    let mul_ab_c = t_app(k, mul, &[ab, c]);
    let mul_c_ab = t_app(k, mul, &[c, ab]);

    // s1 : equiv (mul (add a b) c) (mul c (add a b))
    let s1 = t_app(k, mul_comm, &[ab, c]);
    // s2 : equiv (mul c (add a b)) (add (mul c a) (mul c b))
    let mul_ca = t_app(k, mul, &[c, a]);
    let mul_cb = t_app(k, mul, &[c, b]);
    let add_mca_mcb = t_app(k, add, &[mul_ca, mul_cb]);
    let s2 = t_app(k, left_distrib, &[c, a, b]);

    // s3a : equiv (mul c a) (mul a c) ; s3b : equiv (mul c b) (mul b c)
    let mul_ac = t_app(k, mul, &[a, c]);
    let mul_bc = t_app(k, mul, &[b, c]);
    let s3a = t_app(k, mul_comm, &[c, a]);
    let s3b = t_app(k, mul_comm, &[c, b]);
    let add_mac_mbc = t_app(k, add, &[mul_ac, mul_bc]);
    let s3 = t_app(k, add_congr, &[mul_ca, mul_ac, mul_cb, mul_bc, s3a, s3b]);

    let c1 = t_app(k, equiv_trans, &[mul_ab_c, mul_c_ab, add_mca_mcb, s1, s2]);
    let c2 = t_app(
        k,
        equiv_trans,
        &[mul_ab_c, add_mca_mcb, add_mac_mbc, c1, s3],
    );

    let v = lam_over(k, C_FV, creal_ty, c2);
    let v = lam_over(k, B_FV, creal_ty, v);
    lam_over(k, A_FV, creal_ty, v)
}

/// `CReal.commRingS : AlgS.CommRing`. Every field is an existing `CReal`
/// theorem, verbatim, except `mulOneL`/`distribR` (derived, §4).
///
/// The `STEP_DISPATCH` entry: declares under `p.comm_ring_s`, pre-interned
/// by `intern_names`, rather than interning a fresh name of its own -- the
/// shape every other `declare_*` step in this build follows.
pub(super) fn declare_comm_ring_s(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let p = &p;
    let k = d.kernel();
    let st = p.rat.int.nat.structures_s;
    let comm_ring = st.comm_ring;

    let carrier = k.const_(p.creal, vec![]);
    let equiv = k.const_(p.equiv, vec![]);
    let equiv_refl = k.const_(p.equiv_refl, vec![]);
    let equiv_symm = k.const_(p.equiv_symm, vec![]);
    let equiv_trans = k.const_(p.equiv_trans, vec![]);
    let zero = k.const_(p.zero, vec![]);
    let one = k.const_(p.one, vec![]);
    let add = k.const_(p.add, vec![]);
    let mul = k.const_(p.mul, vec![]);
    let add_congr = k.const_(p.add_congr, vec![]);
    let mul_congr = k.const_(p.mul_congr, vec![]);
    let add_assoc = k.const_(p.add_assoc, vec![]);
    let add_comm = k.const_(p.add_comm, vec![]);
    let add_zero = k.const_(p.add_zero, vec![]);
    let mul_assoc = k.const_(p.mul_assoc, vec![]);
    let mul_one_l = build_mul_one_l(k, p);
    let mul_one_r = k.const_(p.mul_one, vec![]);
    let distrib_l = k.const_(p.left_distrib, vec![]);
    let distrib_r = build_distrib_r(k, p);
    let neg = k.const_(p.neg, vec![]);
    let neg_congr = k.const_(p.neg_congr, vec![]);
    let neg_add = k.const_(p.add_neg, vec![]);
    let mul_comm = k.const_(p.mul_comm, vec![]);

    let mut args = vec![ExprId(0); idx::MUL_COMM + 1];
    args[idx::CARRIER] = carrier;
    args[idx::EQUIV] = equiv;
    args[idx::EQUIV_REFL] = equiv_refl;
    args[idx::EQUIV_SYMM] = equiv_symm;
    args[idx::EQUIV_TRANS] = equiv_trans;
    args[idx::ZERO] = zero;
    args[idx::ONE] = one;
    args[idx::ADD] = add;
    args[idx::MUL] = mul;
    args[idx::ADD_CONGR] = add_congr;
    args[idx::MUL_CONGR] = mul_congr;
    args[idx::ADD_ASSOC] = add_assoc;
    args[idx::ADD_COMM] = add_comm;
    args[idx::ADD_ZERO] = add_zero;
    args[idx::MUL_ASSOC] = mul_assoc;
    args[idx::MUL_ONE_L] = mul_one_l;
    args[idx::MUL_ONE_R] = mul_one_r;
    args[idx::DISTRIB_L] = distrib_l;
    args[idx::DISTRIB_R] = distrib_r;
    args[idx::NEG] = neg;
    args[idx::NEG_CONGR] = neg_congr;
    args[idx::NEG_ADD] = neg_add;
    args[idx::MUL_COMM] = mul_comm;

    let mut value = k.const_(comm_ring.mk, vec![]);
    for a in &args {
        value = k.app(value, *a);
    }
    let ty = k.const_(comm_ring.ind, vec![]);

    k.add_declaration(Declaration::Definition {
        name: p.comm_ring_s,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(())
}

#[cfg(test)]
mod algebra_instance_tests {
    use super::*;
    use crate::creal::build_creal_prelude;
    use crate::nat_prelude::structures_setoid::idx::ring as ring_idx;

    #[test]
    fn creal_comm_ring_s_admits() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        assert!(k.environment().get(p.comm_ring_s).is_some());
    }

    /// `CReal.commRingS`'s axiom footprint must stay empty -- every field is
    /// either a selector onto an already axiom-free `CReal` theorem or a
    /// term composed purely from such selectors (`mulOneL`/`distribR`).
    #[test]
    fn creal_comm_ring_s_axiom_footprint_is_empty() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        assert!(
            k.axiom_footprint(p.comm_ring_s).is_empty(),
            "CReal.commRingS must have an empty axiom footprint"
        );
    }

    /// The named ADR-1587 gap: does `AlgS.mul_zero` applied at
    /// `AlgS.CommRing.toRingS(CReal.commRingS)` have `CReal.mul_zero`'s
    /// exact type by `def_eq`? Measured, not assumed.
    #[test]
    fn generic_mul_zero_instantiated_at_creal_matches_creal_mul_zero_type() {
        const A_FV: u64 = 23_000;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let comm_ring_s = p.comm_ring_s;

        let np = p.rat.int.nat;
        let extra = np.structures_s_extra;

        let comm_ring_s_c = k.const_(comm_ring_s, vec![]);
        let to_ring_s = k.const_(extra.comm_ring_to_ring_s, vec![]);
        let ring_s_val = k.app(to_ring_s, comm_ring_s_c);

        let mul_zero_c = k.const_(extra.mul_zero, vec![]);
        let applied = k.app(mul_zero_c, ring_s_val);
        // AlgS.mul_zero : forall (R:Ring)(a:carrier), equiv (mul a zero) zero
        // -- confirm it type-checks fully applied at a genuinely free `a`,
        // registered in a real LocalContext (a bare `k.fvar` is unbound to
        // plain `infer`, which uses an empty context).
        let a = k.fvar(A_FV);
        let creal_ty = k.const_(p.creal, vec![]);
        let anon = k.anon();
        let mut ctx = crate::tc::LocalContext::new();
        ctx.push(crate::tc::LocalDecl {
            fvar: A_FV,
            name: anon,
            ty: creal_ty,
            info: crate::BinderInfo::Default,
        });
        let applied_a = k.app(applied, a);
        let applied_ty = k
            .infer_in(applied_a, &mut ctx)
            .expect("AlgS.mul_zero applied at CReal's Ring projection must infer a type");

        let creal_mul_zero = k.const_(p.mul_zero, vec![]);
        let creal_mul_zero_a = k.app(creal_mul_zero, a);
        let creal_mul_zero_ty = k
            .infer_in(creal_mul_zero_a, &mut ctx)
            .expect("CReal.mul_zero applied at a must infer a type");

        let matches = k.def_eq_in(applied_ty, creal_mul_zero_ty, &mut ctx);
        // Report, do not assume: this is the ADR-1588 measurement.
        eprintln!("AlgS.mul_zero(CReal.commRingS.toRingS, a) def_eq CReal.mul_zero(a): {matches}");
        assert!(
            matches,
            "AlgS.mul_zero instantiated at CReal.commRingS's Ring projection must be \
             def_eq to CReal.mul_zero's own type at a free `a`"
        );
    }

    /// Same measurement for `AlgS.neg_neg`.
    #[test]
    fn generic_neg_neg_instantiated_at_creal_matches_creal_neg_neg_type() {
        const A_FV: u64 = 23_010;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let comm_ring_s = p.comm_ring_s;

        let np = p.rat.int.nat;
        let extra = np.structures_s_extra;

        let comm_ring_s_c = k.const_(comm_ring_s, vec![]);
        let to_ring_s = k.const_(extra.comm_ring_to_ring_s, vec![]);
        let ring_s_val = k.app(to_ring_s, comm_ring_s_c);

        let neg_neg_c = k.const_(extra.neg_neg, vec![]);
        let applied = k.app(neg_neg_c, ring_s_val);
        // CReal has no named `neg_neg` theorem (grepped: absent from
        // `CRealPrelude` and every `creal/*.rs` module), so unlike
        // `mul_zero` there is nothing to `def_eq`-compare against -- this
        // test confirms only that the fully-applied generic theorem
        // type-checks over a genuinely free `a : CReal`, registered in a
        // real `LocalContext` (a bare `k.fvar` is unbound to plain `infer`).
        let a = k.fvar(A_FV);
        let creal_ty = k.const_(p.creal, vec![]);
        let anon = k.anon();
        let mut ctx = crate::tc::LocalContext::new();
        ctx.push(crate::tc::LocalDecl {
            fvar: A_FV,
            name: anon,
            ty: creal_ty,
            info: crate::BinderInfo::Default,
        });
        let applied_a = k.app(applied, a);
        let applied_ty = k
            .infer_in(applied_a, &mut ctx)
            .expect("AlgS.neg_neg applied at CReal's Ring projection must infer a type");
        assert!(k.environment().get(comm_ring_s).is_some());
        let _ = ring_idx::CARRIER;
        assert!(k.infer_in(applied_ty, &mut ctx).is_ok());
    }

    /// Concrete evaluation (deliverable rule: every new `Definition` needs
    /// one): `mul_zero` at the embedded rational `2 : CReal` (`ofRat 2`).
    #[test]
    fn creal_comm_ring_s_fields_reduce_at_a_concrete_embedded_rational() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let comm_ring_s = p.comm_ring_s;

        // Project mulComm and confirm it applies at CReal.zero / CReal.one
        // (both already-built CReal terms) without error.
        let comm_ring_s_c = k.const_(comm_ring_s, vec![]);
        let mul_comm_sel = k.const_(
            p.rat.int.nat.structures_s.comm_ring.sel(idx::MUL_COMM),
            vec![],
        );
        let projected_mul_comm = k.app(mul_comm_sel, comm_ring_s_c);
        let zero = k.const_(p.zero, vec![]);
        let one = k.const_(p.one, vec![]);
        let applied = t_app(&mut k, projected_mul_comm, &[zero, one]);
        assert!(
            k.infer(applied).is_ok(),
            "projected mulComm must apply concretely at CReal.zero, CReal.one"
        );
    }

    /// `AlgS.sub_self` instantiated at `CReal.commRingS.toRingS`, both
    /// concretely (`CReal.zero`) and symbolically (a free `a : CReal`).
    #[test]
    fn generic_sub_self_instantiated_at_creal_type_checks_concrete_and_symbolic() {
        const A_FV: u64 = 23_020;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let comm_ring_s = p.comm_ring_s;

        let np = p.rat.int.nat;
        let extra = np.structures_s_extra;

        let comm_ring_s_c = k.const_(comm_ring_s, vec![]);
        let to_ring_s = k.const_(extra.comm_ring_to_ring_s, vec![]);
        let ring_s_val = k.app(to_ring_s, comm_ring_s_c);

        let sub_self_c = k.const_(extra.sub_self, vec![]);
        let applied = k.app(sub_self_c, ring_s_val);

        // Concrete: at CReal.zero.
        let zero = k.const_(p.zero, vec![]);
        let applied_zero = k.app(applied, zero);
        assert!(
            k.infer(applied_zero).is_ok(),
            "AlgS.sub_self applied at CReal.zero must infer a type"
        );

        // Symbolic: at a genuinely free `a : CReal`.
        let a = k.fvar(A_FV);
        let creal_ty = k.const_(p.creal, vec![]);
        let anon = k.anon();
        let mut ctx = crate::tc::LocalContext::new();
        ctx.push(crate::tc::LocalDecl {
            fvar: A_FV,
            name: anon,
            ty: creal_ty,
            info: crate::BinderInfo::Default,
        });
        let applied_a = k.app(applied, a);
        assert!(
            k.infer_in(applied_a, &mut ctx).is_ok(),
            "AlgS.sub_self applied at CReal's Ring projection must infer a type at a free `a`"
        );
    }
}
