//! ADR-1627: **ℚ as a vector space over itself**, and the bridge from the
//! abstract `AlgS.Module.linComb` to the concrete `Rat.sumRange` the ℚ linear
//! algebra is built on.
//!
//! # What landed, and what the measurement says about the rest
//!
//! ADR-1609 sized the ℚ bridge in three items and said not to price it as
//! small. Measured here:
//!
//! | item | ADR-1609's estimate | measured |
//! |---|---|---|
//! | 1. an `AlgS.CommRing` value for ℚ | free | free — `AlgS.Field.toCommRing Rat.fieldS` |
//! | 2. `linComb` ↔ `Rat.sumRange` agreement | "`Eq.refl`-adjacent" | **`Eq.refl` exactly** — [`RatVectorSpaceNames::lin_comb_eq_sum_range`] |
//! | 3. `rank`/`nullity` as `spans`/`linearIndependent` | the real cost | **still blocked**, see below |
//!
//! Item 2 is `Eq.refl` because both sides are the SAME `Nat.rec`: `linComb`
//! is `Nat.rec` with base `M.e` and step `fun j ih => M.op ih (smul (c j)
//! (v j))`, and `Rat.sumRange g` is `Nat.rec` with base `Rat.zero` and step
//! `fun j ih => Rat.add ih (g j)`. At `M := AlgS.CommRing.toCommGroupS`
//! of ℚ's ring and `smul := Rat.mul`, every selector ι-reduces and the two
//! minor premises are the same term. The convention match ADR-1609 guessed at
//! — exclusive bound, new term on the right — is real.
//!
//! # Item 3: measured, not promised
//!
//! `Rat.rank M rows cols` is `Nat.countRange (nonzeroRowB (rowEchelon M rows
//! cols) cols) rows` — the number of nonzero rows of the COMPUTED echelon
//! form. To say "`rank` is the dimension of the row space" you must know that
//! `rowEchelon` produces an echelon form, which is
//! `rowEchelon_isEchelon : ∀ A r c, isEchelon (rowEchelon A r c) r c = true`,
//! ADR-1554 obligation 4. ADR-1554 sizes it as "at least a lane on its own and
//! probably two", behind obligations 2 (`pivotSearch`'s postcondition) and 3
//! (`clearBelow`'s postcondition), each also a lane.
//!
//! **That estimate is confirmed, and it is not the only gap.** Even granting
//! `rowEchelon_isEchelon`, the statement "`rank M rows cols` is the cardinality
//! of a basis of the row space" needs, over the layer this lane built:
//!
//! - `AlgS.Module.isBasis` at a family of `Nat -> Rat`-valued vectors, i.e. a
//!   module whose carrier is a FUNCTION type, not `Rat`. `selfModule` gives
//!   ℚ over ℚ; the row space needs ℚ^n, which is `AlgS.CommGroup` over
//!   `Nat -> Rat` and does not exist. That is a fourth item ADR-1609 did not
//!   list, and it is the same "no `funext`" constraint the polynomial ring
//!   met — statable over setoids (pointwise equivalence), so it is work and
//!   not an obstruction.
//! - `AlgS.VectorSpace.basis_zero_unique` generalised to arbitrary length,
//!   i.e. the Steinitz exchange (`nat_prelude::vector_space`'s module doc
//!   sizes that separately).
//!
//! So the honest price of "connect `Rat.rank` to the abstract theorem" is
//! **three open lanes** (ADR-1554 obligations 2, 3, 4) plus ℚ^n as a setoid
//! `AlgS.CommGroup` plus general dimension invariance. Nothing here promises
//! any of them; items 1 and 2 are landed and item 3 is left `open` in the
//! ledger with this measurement attached.

use super::RatPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::structures::{arrow, eq_of, lam_over, pi_over, refl_of};

const C_FV: u64 = 28_000;
const V_FV: u64 = 28_001;
const N_FV: u64 = 28_002;
const I_FV: u64 = 28_003;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

/// Everything this module declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RatVectorSpaceNames {
    /// `Rat.commRingS : AlgS.CommRing` — `AlgS.Field.toCommRing Rat.fieldS`.
    pub comm_ring_s: NameId,
    /// `Rat.addCommGroupS : AlgS.CommGroup` — ℚ's additive group.
    pub add_comm_group_s: NameId,
    /// `Rat.vectorSpaceS : AlgS.VectorSpace.IsVectorSpace Rat.fieldS
    /// Rat.addCommGroupS Rat.mul` — **ℚ is a vector space over itself**.
    pub vector_space_s: NameId,
    /// `Rat.linComb_eq_sumRange` — the concrete/abstract bridge, `Eq.refl`.
    pub lin_comb_eq_sum_range: NameId,
}

/// The `AlgS` names this module reaches, re-derived from the interned root.
struct Algs {
    comm_ring_ind: NameId,
    comm_group_ind: NameId,
    field_to_comm_ring: NameId,
    comm_ring_to_comm_group: NameId,
    is_vector_space: NameId,
    self_module: NameId,
    lin_comb: NameId,
}

fn algs(k: &mut Kernel) -> Algs {
    let anon = k.anon();
    let root = k.name_str(anon, "AlgS");
    let field = k.name_str(root, "Field");
    let comm_ring = k.name_str(root, "CommRing");
    let comm_group = k.name_str(root, "CommGroup");
    let vs = k.name_str(root, "VectorSpace");
    let module = k.name_str(root, "Module");
    Algs {
        comm_ring_ind: comm_ring,
        comm_group_ind: comm_group,
        field_to_comm_ring: k.name_str(field, "toCommRing"),
        comm_ring_to_comm_group: k.name_str(comm_ring, "toCommGroupS"),
        is_vector_space: k.name_str(vs, "IsVectorSpace"),
        self_module: k.name_str(module, "selfModule"),
        lin_comb: k.name_str(module, "linComb"),
    }
}

/// Declare ℚ's ring, additive group, vector-space instance and the bridge.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means
/// [`Kernel::add_declaration`] **refused** a proof term.
pub(crate) fn declare_rat_vector_space(
    k: &mut Kernel,
    p: &RatPrelude,
) -> Result<RatVectorSpaceNames, KernelError> {
    let a = algs(k);
    let lg = p.int.nat.logic;
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let rat = k.const_(p.int.rat, vec![]);
    let nat = k.const_(lg.nat, vec![]);
    let field_s = {
        let n = k.name_str(p.int.rat, "fieldS");
        k.const_(n, vec![])
    };

    // --- 1. `Rat.commRingS := AlgS.Field.toCommRing Rat.fieldS` ------------
    let comm_ring_s = {
        let name = k.name_str(p.int.rat, "commRingS");
        let to_cr = k.const_(a.field_to_comm_ring, vec![]);
        let value = k.app(to_cr, field_s);
        let ty = k.const_(a.comm_ring_ind, vec![]);
        k.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: crate::env::ReducibilityHint::Regular(1),
        })?;
        name
    };

    // --- 2. `Rat.addCommGroupS := AlgS.CommRing.toCommGroupS Rat.commRingS`
    let add_comm_group_s = {
        let name = k.name_str(p.int.rat, "addCommGroupS");
        let to_cg = k.const_(a.comm_ring_to_comm_group, vec![]);
        let ring = k.const_(comm_ring_s, vec![]);
        let value = k.app(to_cg, ring);
        let ty = k.const_(a.comm_group_ind, vec![]);
        k.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: crate::env::ReducibilityHint::Regular(1),
        })?;
        name
    };

    // --- 3. ℚ is a vector space over itself -------------------------------
    let mul = k.const_(p.int.rat_mul, vec![]);
    let vector_space_s = {
        let name = k.name_str(p.int.rat, "vectorSpaceS");
        let ring = k.const_(comm_ring_s, vec![]);
        let group = k.const_(add_comm_group_s, vec![]);
        let value = {
            let t = k.const_(a.self_module, vec![]);
            k.app(t, ring)
        };
        let ty = {
            let t = k.const_(a.is_vector_space, vec![]);
            t_app(k, t, &[field_s, group, mul])
        };
        k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        name
    };

    // --- 4. `linComb` at ℚ IS `Rat.sumRange`, by `Eq.refl` ----------------
    let lin_comb_eq_sum_range = {
        let name = k.name_str(p.int.rat, "linComb_eq_sumRange");
        let fn_ty = arrow(k, nat, rat);
        let c = k.fvar(C_FV);
        let v = k.fvar(V_FV);
        let n = k.fvar(N_FV);
        let ring = k.const_(comm_ring_s, vec![]);
        let group = k.const_(add_comm_group_s, vec![]);
        let lhs = {
            let t = k.const_(a.lin_comb, vec![]);
            t_app(k, t, &[ring, group, mul, c, v, n])
        };
        let rhs = {
            let g = {
                let i = k.fvar(I_FV);
                let ci = k.app(c, i);
                let vi = k.app(v, i);
                let prod = {
                    let e = k.app(mul, ci);
                    k.app(e, vi)
                };
                lam_over(k, I_FV, nat, prod)
            };
            let t = k.const_(p.sum_range, vec![]);
            let e = k.app(t, g);
            k.app(e, n)
        };
        let stmt = eq_of(k, &lg, l1, rat, lhs, rhs);
        let value = refl_of(k, &lg, l1, rat, lhs);
        let value = lam_over(k, N_FV, nat, value);
        let value = lam_over(k, V_FV, fn_ty, value);
        let value = lam_over(k, C_FV, fn_ty, value);
        let ty = pi_over(k, N_FV, nat, stmt);
        let ty = pi_over(k, V_FV, fn_ty, ty);
        let ty = pi_over(k, C_FV, fn_ty, ty);
        k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        name
    };

    Ok(RatVectorSpaceNames {
        comm_ring_s,
        add_comm_group_s,
        vector_space_s,
        lin_comb_eq_sum_range,
    })
}

#[cfg(test)]
#[path = "vector_space_instance_tests.rs"]
mod vector_space_instance_tests;
