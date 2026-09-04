//! `Complex.commRingS : AlgS.CommRing` — the same payoff ADR-1588 built for
//! `CReal` (`creal/algebra_instance.rs`), one carrier up. `Complex` is pairs
//! of `CReal` under the *defined* `Complex.Equiv` (ADR-0521), never `Eq`, so
//! it needs the setoid-flavored `AlgS` spine exactly as `CReal` did.
//!
//! Every field is an *existing* `Complex` theorem, verbatim — the nine
//! commutative-ring laws `complex/ring.rs`'s `declare_ring_laws` proves,
//! `add_congr`/`mul_congr` from the `ComplexPrelude` congruence obligations
//! — except `mulOneL`/`distribR`, each derived by one or three `equivTrans`
//! applications, no new `complex` proof; the derivation is byte-for-byte the
//! same term shape `creal/algebra_instance.rs` uses (`Complex.mul_one` and
//! `Complex.left_distrib` are stated in the identical right/left forms
//! `CReal.mul_one`/`CReal.left_distrib` are, confirmed by reading
//! `declare_ring_laws`'s own proof terms, not assumed from the name).
//!
//! Wired into `build_complex_prelude`'s `STEPS` right after
//! `declare_ring_laws`, the step that provides every ring law field this
//! declaration needs.

use crate::Kernel;
use crate::KernelError;
use crate::complex::ComplexPrelude;
use crate::creal::algebra_instance::{lam_over, t_app};
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures_setoid::idx::comm_ring as idx;

/// `Complex.mulOneL : forall a, Complex.equiv (Complex.mul Complex.one a) a`
/// — derived from `mul_comm(one, a)` and `mul_one(a)`, one `equiv_trans`
/// application, no new `complex` proof. Identical shape to
/// `creal::algebra_instance::build_mul_one_l`.
pub fn build_mul_one_l(k: &mut Kernel, p: &ComplexPrelude) -> ExprId {
    const A_FV: u64 = 24_900;
    let complex_ty = k.const_(p.complex, vec![]);
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
    lam_over(k, A_FV, complex_ty, combined)
}

/// `Complex.distribR : forall a b c, Complex.equiv (Complex.mul (Complex.add
/// a b) c) (Complex.add (Complex.mul a c) (Complex.mul b c))` — derived from
/// `mul_comm` (three applications) and `left_distrib`, via `add_congr`, no
/// new `complex` proof. Identical shape to
/// `creal::algebra_instance::build_distrib_r`.
pub fn build_distrib_r(k: &mut Kernel, p: &ComplexPrelude) -> ExprId {
    const A_FV: u64 = 24_910;
    const B_FV: u64 = 24_911;
    const C_FV: u64 = 24_912;
    let complex_ty = k.const_(p.complex, vec![]);
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

    let v = lam_over(k, C_FV, complex_ty, c2);
    let v = lam_over(k, B_FV, complex_ty, v);
    lam_over(k, A_FV, complex_ty, v)
}

/// `Complex.commRingS : AlgS.CommRing`. Every field is an existing `Complex`
/// theorem, verbatim, except `mulOneL`/`distribR` (derived, above).
///
/// The `STEPS` entry: declares under `p.comm_ring_s`, pre-interned by
/// `intern_names`, the shape every other `declare_*` step in this build
/// follows.
pub(super) fn declare_comm_ring_s(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let p = &p;
    let k = d.kernel();
    let st = p.creal.rat.int.nat.structures_s;
    let comm_ring = st.comm_ring;

    let carrier = k.const_(p.complex, vec![]);
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
    use crate::complex::build_complex_prelude;

    // Every test in this module builds `complex`/`creal` on its own thread via
    // `build_complex_prelude`, and the crate's stack-envelope pin
    // (`artifacts/kernel-stack-envelope.tsv`) shows `complex` debug needs
    // 16,777,216 B -- 8x the 2,097,152 a `#[test]` thread gets by default. A
    // process-wide, in-memory cache (`prelude_cache`, ADR-0464) can make this
    // look free when some OTHER test already warmed it earlier in the same
    // run, which is why this was not seen every time: whichever test is
    // scheduled to build the cold cache first aborts the whole binary
    // (`fatal runtime error: stack overflow`), and the crash names only that
    // one test even though every test here shares the defect. Measured
    // 2026-09-03: `complex_comm_ring_s_admits` aborted a `cargo test -p
    // axeyum-lean-kernel --lib` run at the default stack. All six run on
    // `crate::on_a_deep_stack` so none of them depends on cache-warming luck.
    #[test]
    fn complex_comm_ring_s_admits() {
        crate::on_a_deep_stack(|| {
            let mut k = Kernel::new();
            let p = build_complex_prelude(&mut k).expect("complex prelude must build");
            assert!(k.environment().get(p.comm_ring_s).is_some());
        });
    }

    /// `Complex.commRingS`'s axiom footprint must stay empty -- every field
    /// is either a selector onto an already axiom-free `Complex` theorem or
    /// a term composed purely from such selectors (`mulOneL`/`distribR`).
    #[test]
    fn complex_comm_ring_s_axiom_footprint_is_empty() {
        crate::on_a_deep_stack(|| {
            let mut k = Kernel::new();
            let p = build_complex_prelude(&mut k).expect("complex prelude must build");
            assert!(
                k.axiom_footprint(p.comm_ring_s).is_empty(),
                "Complex.commRingS must have an empty axiom footprint"
            );
        });
    }

    /// Evaluation test (deliverable rule: every new `Definition` needs one):
    /// projecting `mulComm` off `Complex.commRingS` yields, by `def_eq` on
    /// its TYPE, `Complex.mul_comm`'s own rendered type -- confirmed by
    /// reduction, not assumed from the field-index table.
    #[test]
    fn projecting_mul_comm_yields_complex_mul_comm_type() {
        crate::on_a_deep_stack(projecting_mul_comm_yields_complex_mul_comm_type_body);
    }

    fn projecting_mul_comm_yields_complex_mul_comm_type_body() {
        const A_FV: u64 = 24_920;
        const B_FV: u64 = 24_921;
        let mut k = Kernel::new();
        let p = build_complex_prelude(&mut k).expect("complex prelude must build");

        let comm_ring_s_c = k.const_(p.comm_ring_s, vec![]);
        let mul_comm_sel = k.const_(
            p.creal
                .rat
                .int
                .nat
                .structures_s
                .comm_ring
                .sel(idx::MUL_COMM),
            vec![],
        );
        let projected_mul_comm = k.app(mul_comm_sel, comm_ring_s_c);

        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let complex_ty = k.const_(p.complex, vec![]);
        let anon = k.anon();
        let mut ctx = crate::tc::LocalContext::new();
        ctx.push(crate::tc::LocalDecl {
            fvar: A_FV,
            name: anon,
            ty: complex_ty,
            info: crate::BinderInfo::Default,
        });
        ctx.push(crate::tc::LocalDecl {
            fvar: B_FV,
            name: anon,
            ty: complex_ty,
            info: crate::BinderInfo::Default,
        });
        let applied = t_app(&mut k, projected_mul_comm, &[a, b]);
        let projected_ty = k
            .infer_in(applied, &mut ctx)
            .expect("projected mulComm applied at free a, b must infer a type");

        let mul_comm_c = k.const_(p.mul_comm, vec![]);
        let mul_comm_applied = t_app(&mut k, mul_comm_c, &[a, b]);
        let mul_comm_ty = k
            .infer_in(mul_comm_applied, &mut ctx)
            .expect("Complex.mul_comm applied at free a, b must infer a type");

        let matches = k.def_eq_in(projected_ty, mul_comm_ty, &mut ctx);
        eprintln!(
            "AlgS.CommRing.mulComm(Complex.commRingS, a, b) def_eq Complex.mul_comm(a, b): {matches}"
        );
        assert!(
            matches,
            "projected mulComm's type must be def_eq to Complex.mul_comm's own type \
             at free a, b"
        );
    }

    /// Concrete evaluation: `mulComm` applies concretely at `Complex.zero`,
    /// `Complex.one` without error.
    #[test]
    fn complex_comm_ring_s_fields_reduce_at_zero_and_one() {
        crate::on_a_deep_stack(complex_comm_ring_s_fields_reduce_at_zero_and_one_body);
    }

    fn complex_comm_ring_s_fields_reduce_at_zero_and_one_body() {
        let mut k = Kernel::new();
        let p = build_complex_prelude(&mut k).expect("complex prelude must build");

        let comm_ring_s_c = k.const_(p.comm_ring_s, vec![]);
        let mul_comm_sel = k.const_(
            p.creal
                .rat
                .int
                .nat
                .structures_s
                .comm_ring
                .sel(idx::MUL_COMM),
            vec![],
        );
        let projected_mul_comm = k.app(mul_comm_sel, comm_ring_s_c);
        let zero = k.const_(p.zero, vec![]);
        let one = k.const_(p.one, vec![]);
        let applied = t_app(&mut k, projected_mul_comm, &[zero, one]);
        assert!(
            k.infer(applied).is_ok(),
            "projected mulComm must apply concretely at Complex.zero, Complex.one"
        );
    }

    /// Deliverable 5 (ADR-1590): `AlgS.mul_neg_one` instantiated at
    /// `Complex` (`Complex.commRingS.toRingS`), concrete and symbolic.
    /// `Complex` has no named `mul_neg_one`/`neg_one_mul` theorem at all
    /// (grepped: absent from `complex.rs` and every `complex/*.rs`), so
    /// this is well-typedness only.
    #[test]
    fn generic_mul_neg_one_instantiated_at_complex_type_checks_concrete_and_symbolic() {
        crate::on_a_deep_stack(
            generic_mul_neg_one_instantiated_at_complex_type_checks_concrete_and_symbolic_body,
        );
    }

    fn generic_mul_neg_one_instantiated_at_complex_type_checks_concrete_and_symbolic_body() {
        const A_FV: u64 = 24_930;
        let mut k = Kernel::new();
        let p = build_complex_prelude(&mut k).expect("complex prelude must build");

        let np = p.creal.rat.int.nat;
        let extra = np.structures_s_extra;

        let comm_ring_s_c = k.const_(p.comm_ring_s, vec![]);
        let to_ring_s = k.const_(extra.comm_ring_to_ring_s, vec![]);
        let ring_s_val = k.app(to_ring_s, comm_ring_s_c);

        let mul_neg_one_c = k.const_(extra.mul_neg_one, vec![]);
        let applied = k.app(mul_neg_one_c, ring_s_val);

        let zero = k.const_(p.zero, vec![]);
        let applied_zero = k.app(applied, zero);
        assert!(
            k.infer(applied_zero).is_ok(),
            "AlgS.mul_neg_one applied at Complex.zero must infer a type"
        );

        let a = k.fvar(A_FV);
        let complex_ty = k.const_(p.complex, vec![]);
        let anon = k.anon();
        let mut ctx = crate::tc::LocalContext::new();
        ctx.push(crate::tc::LocalDecl {
            fvar: A_FV,
            name: anon,
            ty: complex_ty,
            info: crate::BinderInfo::Default,
        });
        let applied_a = k.app(applied, a);
        assert!(
            k.infer_in(applied_a, &mut ctx).is_ok(),
            "AlgS.mul_neg_one applied at Complex's Ring projection must infer a type at a free `a`"
        );
    }

    /// Deliverable 5 (ADR-1590): `AlgS.add_left_cancel` instantiated at
    /// `Complex`'s additive group, built inline from `Complex.commRingS`'s
    /// Ring fields via `structures_setoid::ring_s_additive_group_value` --
    /// `Complex` has no named `AlgS.Group`/`add_left_cancel` theorem of its
    /// own -- closed over `(a,b,c)`.
    #[test]
    fn generic_add_left_cancel_instantiated_at_complex_type_checks() {
        crate::on_a_deep_stack(generic_add_left_cancel_instantiated_at_complex_type_checks_body);
    }

    fn generic_add_left_cancel_instantiated_at_complex_type_checks_body() {
        const A_FV: u64 = 24_940;
        const B_FV: u64 = 24_941;
        const C_FV: u64 = 24_942;
        let mut k = Kernel::new();
        let p = build_complex_prelude(&mut k).expect("complex prelude must build");

        let np = p.creal.rat.int.nat;
        let extra = np.structures_s_extra;
        let st = np.structures_s;

        let comm_ring_s_c = k.const_(p.comm_ring_s, vec![]);
        let to_ring_s = k.const_(extra.comm_ring_to_ring_s, vec![]);
        let ring_s_val = k.app(to_ring_s, comm_ring_s_c);
        let group_val = crate::nat_prelude::structures_setoid::ring_s_additive_group_value(
            &mut k, &st.ring, &st.group, ring_s_val,
        );

        let add_left_cancel_c = k.const_(extra.add_left_cancel, vec![]);
        let complex_ty = k.const_(p.complex, vec![]);
        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let c = k.fvar(C_FV);
        let generic_applied = {
            let e1 = k.app(add_left_cancel_c, group_val);
            let e2 = k.app(e1, a);
            let e3 = k.app(e2, b);
            k.app(e3, c)
        };
        let generic_closed = {
            let v = generic_applied;
            let v = lam_over(&mut k, C_FV, complex_ty, v);
            let v = lam_over(&mut k, B_FV, complex_ty, v);
            lam_over(&mut k, A_FV, complex_ty, v)
        };
        assert!(
            k.infer(generic_closed).is_ok(),
            "AlgS.add_left_cancel applied at Complex's additive Group value must type-check"
        );
    }
}
