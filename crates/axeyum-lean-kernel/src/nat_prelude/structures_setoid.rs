//! `AlgS.*` — ADR-1588's Setoid-flavored twin of [`super::structures`]'s
//! `Alg.*` spine: nine independent one-constructor `Sort 2` records
//! `Magma -> Semigroup -> Monoid -> CommMonoid -> Group -> CommGroup ->
//! Semiring -> Ring -> CommRing`, each carrying a caller-supplied `equiv`
//! relation (with `equiv_refl`/`equiv_symm`/`equiv_trans` and one
//! congruence field per operation) instead of relying on the kernel's
//! primitive `Eq`, and every law field stated with `equiv` in place of
//! `Eq`.
//!
//! ## Why this exists as a SECOND spine, not a parameter on the first
//!
//! `Alg.*`'s law fields are all `Eq (op a b) (op b a)` — the wrong
//! proposition for a carrier like `CReal` whose equality is a *defined*
//! relation, `CReal.Equiv` (ADR-0512). ADR-1587 §4 measured this directly:
//! `CReal.mul_zero`/`mul_le_mul_of_nonneg_left`/`pow_add` all exist as named
//! theorems but none is a candidate for `Alg.*` retirement, because the
//! whole spine is built on literal `Eq`. This module is the fix ADR-1588
//! designs and builds: a second spine, independent of `Alg.*` (no shared
//! declarations, no coercion — this kernel has none), reusing `Alg.*`'s own
//! `FieldSpec`/`declare_record` machinery (`super::structures`) with LAW
//! fields built by applying the record's own `equiv` VALUE
//! (`app2(k, equiv, lhs, rhs)`) instead of the kernel's `Eq` constant.
//!
//! ## The load-bearing fact this design exploits
//!
//! `app2(k, equiv, lhs, rhs)` BETA-REDUCES to `Eq carrier lhs rhs` exactly
//! when `equiv := @Eq carrier` (a partially-applied `Eq` constant, itself a
//! value of type `carrier -> carrier -> Prop`). So an `AlgS.*` law field's
//! type is, up to that one substitution, the SAME term `Alg.*`'s
//! corresponding law field already has — which is what makes
//! [`ofAlg`]-style projections (§ below, and see `ofalg` submodule) free:
//! every LAW field of the projected record is the source `Alg.*` record's
//! own selector, unchanged, and only the four equiv-infrastructure fields
//! and the per-operation congruence fields need to be freshly built.
//!
//! ## Field layout (each record independent — no inheritance, matching
//! `Alg.*`'s own decision)
//!
//! | record | fields (0-indexed) | count |
//! | --- | --- | --- |
//! | `Magma` | carrier,equiv,equivRefl,equivSymm,equivTrans,op,opCongr | 7 |
//! | `Semigroup` | Magma + assoc | 8 |
//! | `Monoid` | 0-6 as Magma, e,assoc,identL,identR | 11 |
//! | `CommMonoid` | Monoid + comm | 12 |
//! | `Group` | 0-6 as Magma, e,inv,invCongr,assoc,identL,identR,invL,invR | 15 |
//! | `CommGroup` | Group + comm | 16 |
//! | `Semiring` | equiv-infra(5), zero,one,add,mul,addCongr,mulCongr,addAssoc,addComm,addZero,mulAssoc,mulOneL,mulOneR,distribL,distribR | 19 |
//! | `Ring` | Semiring + neg,negCongr,negAdd | 22 |
//! | `CommRing` | Ring + mulComm | 23 |
//!
//! See `docs/research/09-decisions/adr-1588-a-setoid-flavored-alg-spine-for-creal.md`
//! for the design rationale and the measured field-count cost against
//! `Alg.*` (23 vs 16 at `CommRing`: 4 equiv-infrastructure fields + 3
//! congruence fields the `Eq`-flavored spine gets for free).

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;

use super::structures::{
    self, FieldKind, FieldSpec, RecordNames, app2, arrow, congr_arg, declare_record, lam_over,
    pi_over, sel, symm_of, trans_of,
};

// ---------------------------------------------------------------------------
// Field-index convention (fixed across every record in this spine): 0
// carrier, 1 equiv, 2 equivRefl, 3 equivSymm, 4 equivTrans. Every record's
// own operations/laws start at index 5.
// ---------------------------------------------------------------------------

pub const CARRIER: usize = 0;
pub const EQUIV: usize = 1;
#[allow(dead_code)]
pub const EQUIV_REFL: usize = 2;
#[allow(dead_code)]
pub const EQUIV_SYMM: usize = 3;
#[allow(dead_code)]
pub const EQUIV_TRANS: usize = 4;

const V_A: u64 = 9_800;
const V_AP: u64 = 9_801;
const V_B: u64 = 9_802;
const V_BP: u64 = 9_803;
const V_C: u64 = 9_804;

// ---------------------------------------------------------------------------
// Field-shape combinators. Mirror `super::structures`'s combinators exactly
// (same `vals`-driven closure shape), except every LAW field applies the
// record's own `equiv` value (`vals[equiv_idx]`) instead of `eq_of`.
// ---------------------------------------------------------------------------

fn carrier_field_s() -> FieldSpec {
    FieldSpec {
        suffix: "carrier",
        kind: FieldKind::CarrierSort,
        build: Box::new(|k, _lg, l1, _vals| k.sort(l1)),
    }
}

/// `carrier -> carrier -> Prop`.
fn equiv_field_s(carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "equiv",
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

/// `forall a, equiv a a`.
fn equiv_refl_field_s(carrier_idx: usize, equiv_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "equivRefl",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let va = k.fvar(V_A);
            let body = app2(k, equiv, va, va);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a b, equiv a b -> equiv b a`.
fn equiv_symm_field_s(carrier_idx: usize, equiv_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "equivSymm",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let hab = app2(k, equiv, va, vb);
            let hba = app2(k, equiv, vb, va);
            let body = arrow(k, hab, hba);
            let t = pi_over(k, V_B, a_ty, body);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b c, equiv a b -> equiv b c -> equiv a c`.
fn equiv_trans_field_s(carrier_idx: usize, equiv_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: "equivTrans",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let hab = app2(k, equiv, va, vb);
            let hbc = app2(k, equiv, vb, vc);
            let hac = app2(k, equiv, va, vc);
            let inner = arrow(k, hbc, hac);
            let inner2 = arrow(k, hab, inner);
            let t = pi_over(k, V_C, a_ty, inner2);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// A caller-supplied `α -> α -> α`. Identical shape to `Alg.*`'s own
/// `binop_field` (operations need no `equiv` involvement).
fn binop_field_s(name: &'static str, carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[carrier_idx];
            let inner = arrow(k, a, a);
            arrow(k, a, inner)
        }),
    }
}

/// A caller-supplied `α -> α`.
fn unop_field_s(name: &'static str, carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[carrier_idx];
            arrow(k, a, a)
        }),
    }
}

/// A caller-supplied element `: α`.
fn elem_field_s(name: &'static str, carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Data,
        build: Box::new(move |_k, _lg, _l1, vals| vals[carrier_idx]),
    }
}

/// `forall a a' b b', equiv a a' -> equiv b b' -> equiv (op a b) (op a' b')`
/// — the binary-operation congruence field a setoid must carry by hand.
fn binop_congr_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    op_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let op = vals[op_idx];
            let va = k.fvar(V_A);
            let vap = k.fvar(V_AP);
            let vb = k.fvar(V_B);
            let vbp = k.fvar(V_BP);
            let haa = app2(k, equiv, va, vap);
            let hbb = app2(k, equiv, vb, vbp);
            let op_ab = app2(k, op, va, vb);
            let op_apbp = app2(k, op, vap, vbp);
            let concl = app2(k, equiv, op_ab, op_apbp);
            let inner = arrow(k, hbb, concl);
            let inner2 = arrow(k, haa, inner);
            let t = pi_over(k, V_BP, a_ty, inner2);
            let t = pi_over(k, V_B, a_ty, t);
            let t = pi_over(k, V_AP, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a a', equiv a a' -> equiv (op a) (op a')`.
fn unop_congr_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    op_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let op = vals[op_idx];
            let va = k.fvar(V_A);
            let vap = k.fvar(V_AP);
            let haa = app2(k, equiv, va, vap);
            let op_a = k.app(op, va);
            let op_ap = k.app(op, vap);
            let concl = app2(k, equiv, op_a, op_ap);
            let inner = arrow(k, haa, concl);
            let t = pi_over(k, V_AP, a_ty, inner);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b c, equiv (op (op a b) c) (op a (op b c))`.
fn assoc_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    op_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let op = vals[op_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let ab = app2(k, op, va, vb);
            let lhs = app2(k, op, ab, vc);
            let bc = app2(k, op, vb, vc);
            let rhs = app2(k, op, va, bc);
            let body = app2(k, equiv, lhs, rhs);
            let t = pi_over(k, V_C, a_ty, body);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b, equiv (op a b) (op b a)`.
fn comm_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    op_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let op = vals[op_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let lhs = app2(k, op, va, vb);
            let rhs = app2(k, op, vb, va);
            let body = app2(k, equiv, lhs, rhs);
            let t = pi_over(k, V_B, a_ty, body);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a, equiv (op unit a) a`.
fn unit_left_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    op_idx: usize,
    unit_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let op = vals[op_idx];
            let unit = vals[unit_idx];
            let va = k.fvar(V_A);
            let lhs = app2(k, op, unit, va);
            let body = app2(k, equiv, lhs, va);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a, equiv (op a unit) a`.
fn unit_right_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    op_idx: usize,
    unit_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let op = vals[op_idx];
            let unit = vals[unit_idx];
            let va = k.fvar(V_A);
            let lhs = app2(k, op, va, unit);
            let body = app2(k, equiv, lhs, va);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a, equiv (op (inv a) a) e`.
fn inv_left_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    op_idx: usize,
    inv_idx: usize,
    e_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let op = vals[op_idx];
            let inv = vals[inv_idx];
            let e = vals[e_idx];
            let va = k.fvar(V_A);
            let ia = k.app(inv, va);
            let lhs = app2(k, op, ia, va);
            let body = app2(k, equiv, lhs, e);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a, equiv (op a (inv a)) e`.
fn inv_right_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    op_idx: usize,
    inv_idx: usize,
    e_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let op = vals[op_idx];
            let inv = vals[inv_idx];
            let e = vals[e_idx];
            let va = k.fvar(V_A);
            let ia = k.app(inv, va);
            let lhs = app2(k, op, va, ia);
            let body = app2(k, equiv, lhs, e);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a b c, equiv (mul a (add b c)) (add (mul a b) (mul a c))`.
fn distrib_left_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    add_idx: usize,
    mul_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let add = vals[add_idx];
            let mul = vals[mul_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let bc = app2(k, add, vb, vc);
            let lhs = app2(k, mul, va, bc);
            let ab = app2(k, mul, va, vb);
            let ac = app2(k, mul, va, vc);
            let rhs = app2(k, add, ab, ac);
            let body = app2(k, equiv, lhs, rhs);
            let t = pi_over(k, V_C, a_ty, body);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b c, equiv (mul (add a b) c) (add (mul a c) (mul b c))`.
fn distrib_right_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    add_idx: usize,
    mul_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let add = vals[add_idx];
            let mul = vals[mul_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let ab = app2(k, add, va, vb);
            let lhs = app2(k, mul, ab, vc);
            let ac = app2(k, mul, va, vc);
            let bc = app2(k, mul, vb, vc);
            let rhs = app2(k, add, ac, bc);
            let body = app2(k, equiv, lhs, rhs);
            let t = pi_over(k, V_C, a_ty, body);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a, equiv (add a (neg a)) zero`.
fn neg_add_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    add_idx: usize,
    neg_idx: usize,
    zero_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let add = vals[add_idx];
            let neg = vals[neg_idx];
            let zero = vals[zero_idx];
            let va = k.fvar(V_A);
            let na = k.app(neg, va);
            let lhs = app2(k, add, va, na);
            let body = app2(k, equiv, lhs, zero);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

// ---------------------------------------------------------------------------
// The nine field lists.
// ---------------------------------------------------------------------------

fn magma_fields_s() -> Vec<FieldSpec> {
    vec![
        carrier_field_s(),
        equiv_field_s(CARRIER),
        equiv_refl_field_s(CARRIER, EQUIV),
        equiv_symm_field_s(CARRIER, EQUIV),
        equiv_trans_field_s(CARRIER, EQUIV),
        binop_field_s("op", CARRIER),
        binop_congr_field_s("opCongr", CARRIER, EQUIV, 5),
    ]
}

fn semigroup_fields_s() -> Vec<FieldSpec> {
    let mut f = magma_fields_s();
    f.push(assoc_field_s("assoc", CARRIER, EQUIV, 5));
    f
}

fn monoid_fields_s() -> Vec<FieldSpec> {
    let mut f = magma_fields_s(); // 0..6: carrier,equiv,refl,symm,trans,op,opCongr
    f.push(elem_field_s("e", CARRIER)); // 7
    f.push(assoc_field_s("assoc", CARRIER, EQUIV, 5)); // 8
    f.push(unit_left_field_s("identL", CARRIER, EQUIV, 5, 7)); // 9
    f.push(unit_right_field_s("identR", CARRIER, EQUIV, 5, 7)); // 10
    f
}

fn comm_monoid_fields_s() -> Vec<FieldSpec> {
    let mut f = monoid_fields_s();
    f.push(comm_field_s("comm", CARRIER, EQUIV, 5)); // 11
    f
}

fn group_fields_s() -> Vec<FieldSpec> {
    let mut f = magma_fields_s(); // 0..6
    f.push(elem_field_s("e", CARRIER)); // 7
    f.push(unop_field_s("inv", CARRIER)); // 8
    f.push(unop_congr_field_s("invCongr", CARRIER, EQUIV, 8)); // 9
    f.push(assoc_field_s("assoc", CARRIER, EQUIV, 5)); // 10
    f.push(unit_left_field_s("identL", CARRIER, EQUIV, 5, 7)); // 11
    f.push(unit_right_field_s("identR", CARRIER, EQUIV, 5, 7)); // 12
    f.push(inv_left_field_s("invL", CARRIER, EQUIV, 5, 8, 7)); // 13
    f.push(inv_right_field_s("invR", CARRIER, EQUIV, 5, 8, 7)); // 14
    f
}

fn comm_group_fields_s() -> Vec<FieldSpec> {
    let mut f = group_fields_s();
    f.push(comm_field_s("comm", CARRIER, EQUIV, 5)); // 15
    f
}

fn semiring_fields_s() -> Vec<FieldSpec> {
    vec![
        carrier_field_s(),                                       // 0
        equiv_field_s(CARRIER),                                  // 1
        equiv_refl_field_s(CARRIER, EQUIV),                      // 2
        equiv_symm_field_s(CARRIER, EQUIV),                      // 3
        equiv_trans_field_s(CARRIER, EQUIV),                     // 4
        elem_field_s("zero", CARRIER),                           // 5
        elem_field_s("one", CARRIER),                            // 6
        binop_field_s("add", CARRIER),                           // 7
        binop_field_s("mul", CARRIER),                           // 8
        binop_congr_field_s("addCongr", CARRIER, EQUIV, 7),      // 9
        binop_congr_field_s("mulCongr", CARRIER, EQUIV, 8),      // 10
        assoc_field_s("addAssoc", CARRIER, EQUIV, 7),            // 11
        comm_field_s("addComm", CARRIER, EQUIV, 7),              // 12
        unit_right_field_s("addZero", CARRIER, EQUIV, 7, 5),     // 13
        assoc_field_s("mulAssoc", CARRIER, EQUIV, 8),            // 14
        unit_left_field_s("mulOneL", CARRIER, EQUIV, 8, 6),      // 15
        unit_right_field_s("mulOneR", CARRIER, EQUIV, 8, 6),     // 16
        distrib_left_field_s("distribL", CARRIER, EQUIV, 7, 8),  // 17
        distrib_right_field_s("distribR", CARRIER, EQUIV, 7, 8), // 18
    ]
}

fn ring_fields_s() -> Vec<FieldSpec> {
    let mut f = semiring_fields_s();
    f.push(unop_field_s("neg", CARRIER)); // 19
    f.push(unop_congr_field_s("negCongr", CARRIER, EQUIV, 19)); // 20
    f.push(neg_add_field_s("negAdd", CARRIER, EQUIV, 7, 19, 5)); // 21
    f
}

fn comm_ring_fields_s() -> Vec<FieldSpec> {
    let mut f = ring_fields_s();
    f.push(comm_field_s("mulComm", CARRIER, EQUIV, 8)); // 22
    f
}

/// Field-index constants, one module per record (mirrors
/// `super::structures::idx` exactly). `#[allow(dead_code)]` because not
/// every record's every index has a consumer yet.
#[allow(dead_code, unused_imports)]
pub mod idx {
    pub mod magma {
        pub const CARRIER: usize = 0;
        pub const EQUIV: usize = 1;
        pub const EQUIV_REFL: usize = 2;
        pub const EQUIV_SYMM: usize = 3;
        pub const EQUIV_TRANS: usize = 4;
        pub const OP: usize = 5;
        pub const OP_CONGR: usize = 6;
    }
    pub mod semigroup {
        pub use super::magma::*;
        pub const ASSOC: usize = 7;
    }
    pub mod monoid {
        pub use super::magma::*;
        pub const E: usize = 7;
        pub const ASSOC: usize = 8;
        pub const IDENT_L: usize = 9;
        pub const IDENT_R: usize = 10;
    }
    pub mod comm_monoid {
        pub use super::monoid::*;
        pub const COMM: usize = 11;
    }
    pub mod group {
        pub use super::magma::*;
        pub const E: usize = 7;
        pub const INV: usize = 8;
        pub const INV_CONGR: usize = 9;
        pub const ASSOC: usize = 10;
        pub const IDENT_L: usize = 11;
        pub const IDENT_R: usize = 12;
        pub const INV_L: usize = 13;
        pub const INV_R: usize = 14;
    }
    pub mod comm_group {
        pub use super::group::*;
        pub const COMM: usize = 15;
    }
    pub mod semiring {
        pub const CARRIER: usize = 0;
        pub const EQUIV: usize = 1;
        pub const EQUIV_REFL: usize = 2;
        pub const EQUIV_SYMM: usize = 3;
        pub const EQUIV_TRANS: usize = 4;
        pub const ZERO: usize = 5;
        pub const ONE: usize = 6;
        pub const ADD: usize = 7;
        pub const MUL: usize = 8;
        pub const ADD_CONGR: usize = 9;
        pub const MUL_CONGR: usize = 10;
        pub const ADD_ASSOC: usize = 11;
        pub const ADD_COMM: usize = 12;
        pub const ADD_ZERO: usize = 13;
        pub const MUL_ASSOC: usize = 14;
        pub const MUL_ONE_L: usize = 15;
        pub const MUL_ONE_R: usize = 16;
        pub const DISTRIB_L: usize = 17;
        pub const DISTRIB_R: usize = 18;
    }
    pub mod ring {
        pub use super::semiring::*;
        pub const NEG: usize = 19;
        pub const NEG_CONGR: usize = 20;
        pub const NEG_ADD: usize = 21;
    }
    pub mod comm_ring {
        pub use super::ring::*;
        pub const MUL_COMM: usize = 22;
    }
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuresSNames {
    pub algs: NameId,
    pub magma: NameId,
    pub semigroup: NameId,
    pub monoid: NameId,
    pub comm_monoid: NameId,
    pub group: NameId,
    pub comm_group: NameId,
    pub semiring: NameId,
    pub ring: NameId,
    pub comm_ring: NameId,
}

/// Intern the nine record names under a fresh `AlgS` root — never `Alg`, so
/// this spine cannot collide with `super::structures`'s.
pub(crate) fn intern_structures_s_names(kernel: &mut Kernel) -> StructuresSNames {
    let anon = kernel.anon();
    let algs = kernel.name_str(anon, "AlgS");
    StructuresSNames {
        algs,
        magma: kernel.name_str(algs, "Magma"),
        semigroup: kernel.name_str(algs, "Semigroup"),
        monoid: kernel.name_str(algs, "Monoid"),
        comm_monoid: kernel.name_str(algs, "CommMonoid"),
        group: kernel.name_str(algs, "Group"),
        comm_group: kernel.name_str(algs, "CommGroup"),
        semiring: kernel.name_str(algs, "Semiring"),
        ring: kernel.name_str(algs, "Ring"),
        comm_ring: kernel.name_str(algs, "CommRing"),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuresSRecordNames {
    pub magma: RecordNames,
    pub semigroup: RecordNames,
    pub monoid: RecordNames,
    pub comm_monoid: RecordNames,
    pub group: RecordNames,
    pub comm_group: RecordNames,
    pub semiring: RecordNames,
    pub ring: RecordNames,
    pub comm_ring: RecordNames,
}

/// Declare all nine `AlgS.*` records, each with the same `Sort 1`-refused
/// universe control [`declare_record`] runs for every record it builds.
pub(crate) fn declare_structures_s_all(
    kernel: &mut Kernel,
    p: &StructuresSNames,
    logic: &LogicPrelude,
) -> Result<StructuresSRecordNames, KernelError> {
    let l0 = kernel.level_zero();
    let l1 = kernel.level_succ(l0);
    let l2 = kernel.level_succ(l1);

    let magma = declare_record(kernel, logic, l0, l1, l2, p.magma, &magma_fields_s())?;
    let semigroup = declare_record(
        kernel,
        logic,
        l0,
        l1,
        l2,
        p.semigroup,
        &semigroup_fields_s(),
    )?;
    let monoid = declare_record(kernel, logic, l0, l1, l2, p.monoid, &monoid_fields_s())?;
    let comm_monoid = declare_record(
        kernel,
        logic,
        l0,
        l1,
        l2,
        p.comm_monoid,
        &comm_monoid_fields_s(),
    )?;
    let group = declare_record(kernel, logic, l0, l1, l2, p.group, &group_fields_s())?;
    let comm_group = declare_record(
        kernel,
        logic,
        l0,
        l1,
        l2,
        p.comm_group,
        &comm_group_fields_s(),
    )?;
    let semiring = declare_record(kernel, logic, l0, l1, l2, p.semiring, &semiring_fields_s())?;
    let ring = declare_record(kernel, logic, l0, l1, l2, p.ring, &ring_fields_s())?;
    let comm_ring = declare_record(
        kernel,
        logic,
        l0,
        l1,
        l2,
        p.comm_ring,
        &comm_ring_fields_s(),
    )?;

    Ok(StructuresSRecordNames {
        magma,
        semigroup,
        monoid,
        comm_monoid,
        group,
        comm_group,
        semiring,
        ring,
        comm_ring,
    })
}

// ---------------------------------------------------------------------------
// `AlgS.CommRing.toRingS` — the one forgetful projection this ADR needs: a
// PREFIX projection (`CommRing`'s first 22 fields ARE `Ring`'s field list
// verbatim), the same shape `Alg.CommRing.toRing` uses (ADR-1584).
// ---------------------------------------------------------------------------

pub(crate) fn declare_comm_ring_to_ring_s(
    k: &mut Kernel,
    st: &StructuresSRecordNames,
    p: &StructuresSNames,
) -> Result<NameId, KernelError> {
    use idx::ring::NEG_ADD;
    const R_FV: u64 = 21_000;
    let r = k.fvar(R_FV);
    let mut args = Vec::with_capacity(NEG_ADD + 1);
    for i in 0..=NEG_ADD {
        args.push(sel(k, &st.comm_ring, i, r));
    }
    let value = structures::mk_instance(k, &st.ring, &args);
    let comm_ring_ty0 = k.const_(st.comm_ring.ind, vec![]);
    let value = lam_over(k, R_FV, comm_ring_ty0, value);
    let ty = {
        let r2 = k.fvar(R_FV);
        let dom = k.const_(st.comm_ring.ind, vec![]);
        let cod = k.const_(st.ring.ind, vec![]);
        let _ = r2;
        arrow(k, dom, cod)
    };
    let name = k.name_str(p.comm_ring, "toRingS");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// Build an `AlgS.Group` VALUE (the additive group of a ring), from an
/// `AlgS.Ring` value `r` -- ADR-1590, deliverable 5's plumbing for
/// instantiating `AlgS.add_left_cancel` at a carrier whose only `AlgS`
/// instance is a `CommRing`/`Ring` (`CReal`, `Complex`), which have no
/// named `Group` value of their own. `identL`/`invL` are DERIVED from
/// `addComm`+`addZero`/`negAdd`, the same technique `Alg.Ring.toCommGroup`
/// uses on the `Eq`-flavored spine (ADR-1584), ported to `equivTrans`.
///
/// **Not a declared kernel name** (no `add_declaration` call) -- a
/// reusable term-builder, the same shape `t_app`/`sel` already are, kept
/// deliberately un-named rather than promoted to a formal `Ring.
/// toCommGroupS` projection (out of scope here; ADR-1588 built only the
/// ONE projection its own payoff needed, `CommRing.toRingS`).
///
/// `#[cfg(test)]`: every current consumer is a test in `creal::
/// algebra_instance`/`complex::algebra_instance` (there is no non-test
/// route that needs a `CReal`/`Complex` `Group` value yet); a `cargo
/// clippy --lib --tests` build compiles the plain `--lib` target
/// SEPARATELY from the cfg(test) one, and flags this `pub(crate)` fn dead
/// in that separate artifact if it is not cfg-gated.
#[cfg(test)]
pub(crate) fn ring_s_additive_group_value(
    k: &mut Kernel,
    ring: &RecordNames,
    group: &RecordNames,
    r: ExprId,
) -> ExprId {
    use idx::ring as ridx;
    const A_FV: u64 = 21_400;
    const B_FV: u64 = 21_401;

    let carrier = sel(k, ring, ridx::CARRIER, r);
    let equiv = sel(k, ring, ridx::EQUIV, r);
    let equiv_refl = sel(k, ring, ridx::EQUIV_REFL, r);
    let equiv_symm = sel(k, ring, ridx::EQUIV_SYMM, r);
    let equiv_trans = sel(k, ring, ridx::EQUIV_TRANS, r);
    let add = sel(k, ring, ridx::ADD, r);
    let add_congr = sel(k, ring, ridx::ADD_CONGR, r);
    let zero = sel(k, ring, ridx::ZERO, r);
    let neg = sel(k, ring, ridx::NEG, r);
    let neg_congr = sel(k, ring, ridx::NEG_CONGR, r);
    let add_assoc = sel(k, ring, ridx::ADD_ASSOC, r);
    let add_comm = sel(k, ring, ridx::ADD_COMM, r);
    let add_zero = sel(k, ring, ridx::ADD_ZERO, r); // identR
    let neg_add = sel(k, ring, ridx::NEG_ADD, r); // invR

    // identL(a) : equiv (add zero a) a, via addComm(zero,a); addZero(a).
    let a = k.fvar(A_FV);
    let comm_za = t_app(k, add_comm, &[zero, a]);
    let add_za = t_app(k, add, &[zero, a]);
    let add_az = t_app(k, add, &[a, zero]);
    let az_a = k.app(add_zero, a);
    let ident_l_body = t_app(k, equiv_trans, &[add_za, add_az, a, comm_za, az_a]);
    let ident_l = lam_over(k, A_FV, carrier, ident_l_body);

    // invL(b) : equiv (add (neg b) b) zero, via addComm(neg b,b); negAdd(b).
    let b = k.fvar(B_FV);
    let nb = k.app(neg, b);
    let comm_nb_b = t_app(k, add_comm, &[nb, b]);
    let add_nbb = t_app(k, add, &[nb, b]);
    let add_bnb = t_app(k, add, &[b, nb]);
    let na_b = k.app(neg_add, b);
    let inv_l_body = t_app(k, equiv_trans, &[add_nbb, add_bnb, zero, comm_nb_b, na_b]);
    let inv_l = lam_over(k, B_FV, carrier, inv_l_body);

    structures::mk_instance(
        k,
        group,
        &[
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            add,
            add_congr,
            zero,
            neg,
            neg_congr,
            add_assoc,
            ident_l,
            add_zero,
            inv_l,
            neg_add,
        ],
    )
}

// ---------------------------------------------------------------------------
// `ofAlg` projections: `AlgS.<Record>.ofAlg : Alg.<Record> -> AlgS.<Record>`.
// `equiv := @Eq carrier`; `equivRefl`/`equivSymm`/`equivTrans` and every
// congruence field are synthesized ONCE per shape; every LAW field is the
// source record's own selector, unchanged (see module doc).
// ---------------------------------------------------------------------------
pub mod ofalg {
    use super::{
        Declaration, ExprId, Kernel, KernelError, LevelId, LogicPrelude, NameId, RecordNames,
        ReducibilityHint, app2, arrow, congr_arg, lam_over, sel, structures, symm_of, trans_of,
    };

    /// `@Eq carrier : carrier -> carrier -> Prop`.
    fn eq_partial(k: &mut Kernel, lg: &LogicPrelude, lvl: LevelId, carrier: ExprId) -> ExprId {
        let c = k.const_(lg.eq, vec![lvl]);
        k.app(c, carrier)
    }

    /// `fun a => @Eq.refl carrier a : forall a, equiv a a`.
    fn build_equiv_refl(
        k: &mut Kernel,
        lg: &LogicPrelude,
        lvl: LevelId,
        carrier: ExprId,
    ) -> ExprId {
        k.const_(lg.eq_refl, vec![lvl]).pipe(|c| k.app(c, carrier))
    }

    /// `fun a b h => Eq.symm h : forall a b, equiv a b -> equiv b a`.
    fn build_equiv_symm(
        k: &mut Kernel,
        lg: &LogicPrelude,
        lvl: LevelId,
        carrier: ExprId,
    ) -> ExprId {
        const A: u64 = 21_100;
        const B: u64 = 21_101;
        const H: u64 = 21_102;
        let a = k.fvar(A);
        let b = k.fvar(B);
        let h = k.fvar(H);
        let hyp_ty = crate::nat_prelude::structures::eq_of(k, lg, lvl, carrier, a, b);
        let body = symm_of(k, lg, lvl, carrier, a, b, h);
        let v = lam_over(k, H, hyp_ty, body);
        let v = lam_over(k, B, carrier, v);
        lam_over(k, A, carrier, v)
    }

    /// `fun a b c h1 h2 => Eq.trans h1 h2 : forall a b c, equiv a b -> equiv b c -> equiv a c`.
    fn build_equiv_trans(
        k: &mut Kernel,
        lg: &LogicPrelude,
        lvl: LevelId,
        carrier: ExprId,
    ) -> ExprId {
        const A: u64 = 21_110;
        const B: u64 = 21_111;
        const C: u64 = 21_112;
        const H1: u64 = 21_113;
        const H2: u64 = 21_114;
        const SCRATCH: u64 = 21_115;
        let a = k.fvar(A);
        let b = k.fvar(B);
        let c = k.fvar(C);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let hyp1_ty = crate::nat_prelude::structures::eq_of(k, lg, lvl, carrier, a, b);
        let hyp2_ty = crate::nat_prelude::structures::eq_of(k, lg, lvl, carrier, b, c);
        let body = trans_of(k, lg, lvl, carrier, a, b, c, h1, h2, SCRATCH);
        let v = lam_over(k, H2, hyp2_ty, body);
        let v = lam_over(k, H1, hyp1_ty, v);
        let v = lam_over(k, C, carrier, v);
        let v = lam_over(k, B, carrier, v);
        lam_over(k, A, carrier, v)
    }

    /// `fun a a' h => congr_arg op h : forall a a', equiv a a' -> equiv (op a) (op a')`.
    fn build_unop_congr(
        k: &mut Kernel,
        lg: &LogicPrelude,
        lvl: LevelId,
        carrier: ExprId,
        op: ExprId,
    ) -> ExprId {
        const A: u64 = 21_120;
        const AP: u64 = 21_121;
        const H: u64 = 21_122;
        const SCRATCH: u64 = 21_123;
        let a = k.fvar(A);
        let ap = k.fvar(AP);
        let h = k.fvar(H);
        let hyp_ty = crate::nat_prelude::structures::eq_of(k, lg, lvl, carrier, a, ap);
        let body = congr_arg(k, lg, lvl, carrier, a, ap, h, SCRATCH, &|k2, w| {
            k2.app(op, w)
        });
        let v = lam_over(k, H, hyp_ty, body);
        let v = lam_over(k, AP, carrier, v);
        lam_over(k, A, carrier, v)
    }

    /// `forall a a' b b', equiv a a' -> equiv b b' -> equiv (op a b) (op a' b')`.
    fn build_binop_congr(
        k: &mut Kernel,
        lg: &LogicPrelude,
        lvl: LevelId,
        carrier: ExprId,
        op: ExprId,
    ) -> ExprId {
        const A: u64 = 21_130;
        const AP: u64 = 21_131;
        const B: u64 = 21_132;
        const BP: u64 = 21_133;
        const H1: u64 = 21_134;
        const H2: u64 = 21_135;
        const S1: u64 = 21_136;
        const S2: u64 = 21_137;
        let a = k.fvar(A);
        let ap = k.fvar(AP);
        let b = k.fvar(B);
        let bp = k.fvar(BP);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let hyp1_ty = crate::nat_prelude::structures::eq_of(k, lg, lvl, carrier, a, ap);
        let hyp2_ty = crate::nat_prelude::structures::eq_of(k, lg, lvl, carrier, b, bp);

        let op_ab = app2(k, op, a, b);
        let op_apb = app2(k, op, ap, b);
        // step1 : Eq (op a b) (op a' b)
        let step1 = congr_arg(k, lg, lvl, carrier, a, ap, h1, S1, &|k2, w| {
            app2(k2, op, w, b)
        });
        // step2 : Eq (op a' b) (op a' b')
        let op_apbp = app2(k, op, ap, bp);
        let step2 = congr_arg(k, lg, lvl, carrier, b, bp, h2, S2, &|k2, w| {
            app2(k2, op, ap, w)
        });
        let combined = trans_of(
            k, lg, lvl, carrier, op_ab, op_apb, op_apbp, step1, step2, S1,
        );

        let v = lam_over(k, H2, hyp2_ty, combined);
        let v = lam_over(k, H1, hyp1_ty, v);
        let v = lam_over(k, BP, carrier, v);
        let v = lam_over(k, B, carrier, v);
        let v = lam_over(k, AP, carrier, v);
        lam_over(k, A, carrier, v)
    }

    trait Pipe: Sized {
        fn pipe<R>(self, f: impl FnOnce(Self) -> R) -> R {
            f(self)
        }
    }
    impl<T> Pipe for T {}

    fn declare_projection(
        k: &mut Kernel,
        alg_root_name: NameId,
        src: &RecordNames,
        dst: &RecordNames,
        args: &[ExprId],
        r_fv: u64,
    ) -> Result<NameId, KernelError> {
        let value = structures::mk_instance(k, dst, args);
        let src_ty = k.const_(src.ind, vec![]);
        let value = lam_over(k, r_fv, src_ty, value);
        let dst_ty = k.const_(dst.ind, vec![]);
        let ty = arrow(k, src_ty, dst_ty);
        let name = k.name_str(alg_root_name, "ofAlg");
        k.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
        Ok(name)
    }

    /// `AlgS.Magma.ofAlg : Alg.Magma -> AlgS.Magma`.
    pub(crate) fn declare_magma_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_magma: &RecordNames,
        algs_magma: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::magma::{CARRIER, OP};
        const R_FV: u64 = 21_200;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_magma, CARRIER, r);
        let op = sel(k, alg_magma, OP, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let op_congr = build_binop_congr(k, lg, l1, carrier, op);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            op,
            op_congr,
        ];
        declare_projection(k, algs_p, alg_magma, algs_magma, &args, R_FV)
    }

    /// `AlgS.Semigroup.ofAlg`.
    pub(crate) fn declare_semigroup_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_sg: &RecordNames,
        algs_sg: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::semigroup::{ASSOC, CARRIER, OP};
        const R_FV: u64 = 21_210;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_sg, CARRIER, r);
        let op = sel(k, alg_sg, OP, r);
        let assoc = sel(k, alg_sg, ASSOC, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let op_congr = build_binop_congr(k, lg, l1, carrier, op);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            op,
            op_congr,
            assoc,
        ];
        declare_projection(k, algs_p, alg_sg, algs_sg, &args, R_FV)
    }

    /// `AlgS.Monoid.ofAlg`.
    pub(crate) fn declare_monoid_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_m: &RecordNames,
        algs_m: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::monoid::{
            ASSOC, CARRIER, E, IDENT_L, IDENT_R, OP,
        };
        const R_FV: u64 = 21_220;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_m, CARRIER, r);
        let op = sel(k, alg_m, OP, r);
        let e = sel(k, alg_m, E, r);
        let assoc = sel(k, alg_m, ASSOC, r);
        let ident_l = sel(k, alg_m, IDENT_L, r);
        let ident_r = sel(k, alg_m, IDENT_R, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let op_congr = build_binop_congr(k, lg, l1, carrier, op);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            op,
            op_congr,
            e,
            assoc,
            ident_l,
            ident_r,
        ];
        declare_projection(k, algs_p, alg_m, algs_m, &args, R_FV)
    }

    /// `AlgS.CommMonoid.ofAlg`.
    pub(crate) fn declare_comm_monoid_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_cm: &RecordNames,
        algs_cm: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::comm_monoid::{
            ASSOC, CARRIER, COMM, E, IDENT_L, IDENT_R, OP,
        };
        const R_FV: u64 = 21_230;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_cm, CARRIER, r);
        let op = sel(k, alg_cm, OP, r);
        let e = sel(k, alg_cm, E, r);
        let assoc = sel(k, alg_cm, ASSOC, r);
        let ident_l = sel(k, alg_cm, IDENT_L, r);
        let ident_r = sel(k, alg_cm, IDENT_R, r);
        let comm = sel(k, alg_cm, COMM, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let op_congr = build_binop_congr(k, lg, l1, carrier, op);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            op,
            op_congr,
            e,
            assoc,
            ident_l,
            ident_r,
            comm,
        ];
        declare_projection(k, algs_p, alg_cm, algs_cm, &args, R_FV)
    }

    /// `AlgS.Group.ofAlg`.
    pub(crate) fn declare_group_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_g: &RecordNames,
        algs_g: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::group::{
            ASSOC, CARRIER, E, IDENT_L, IDENT_R, INV, INV_L, INV_R, OP,
        };
        const R_FV: u64 = 21_240;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_g, CARRIER, r);
        let op = sel(k, alg_g, OP, r);
        let e = sel(k, alg_g, E, r);
        let inv = sel(k, alg_g, INV, r);
        let assoc = sel(k, alg_g, ASSOC, r);
        let ident_l = sel(k, alg_g, IDENT_L, r);
        let ident_r = sel(k, alg_g, IDENT_R, r);
        let inv_l = sel(k, alg_g, INV_L, r);
        let inv_r = sel(k, alg_g, INV_R, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let op_congr = build_binop_congr(k, lg, l1, carrier, op);
        let inv_congr = build_unop_congr(k, lg, l1, carrier, inv);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            op,
            op_congr,
            e,
            inv,
            inv_congr,
            assoc,
            ident_l,
            ident_r,
            inv_l,
            inv_r,
        ];
        declare_projection(k, algs_p, alg_g, algs_g, &args, R_FV)
    }

    /// `AlgS.CommGroup.ofAlg`.
    pub(crate) fn declare_comm_group_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_cg: &RecordNames,
        algs_cg: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::comm_group::{
            ASSOC, CARRIER, COMM, E, IDENT_L, IDENT_R, INV, INV_L, INV_R, OP,
        };
        const R_FV: u64 = 21_250;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_cg, CARRIER, r);
        let op = sel(k, alg_cg, OP, r);
        let e = sel(k, alg_cg, E, r);
        let inv = sel(k, alg_cg, INV, r);
        let assoc = sel(k, alg_cg, ASSOC, r);
        let ident_l = sel(k, alg_cg, IDENT_L, r);
        let ident_r = sel(k, alg_cg, IDENT_R, r);
        let inv_l = sel(k, alg_cg, INV_L, r);
        let inv_r = sel(k, alg_cg, INV_R, r);
        let comm = sel(k, alg_cg, COMM, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let op_congr = build_binop_congr(k, lg, l1, carrier, op);
        let inv_congr = build_unop_congr(k, lg, l1, carrier, inv);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            op,
            op_congr,
            e,
            inv,
            inv_congr,
            assoc,
            ident_l,
            ident_r,
            inv_l,
            inv_r,
            comm,
        ];
        declare_projection(k, algs_p, alg_cg, algs_cg, &args, R_FV)
    }

    /// `AlgS.Semiring.ofAlg`.
    pub(crate) fn declare_semiring_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_sr: &RecordNames,
        algs_sr: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::semiring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_ONE_L, MUL_ONE_R, ONE, ZERO,
        };
        const R_FV: u64 = 21_260;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_sr, CARRIER, r);
        let zero = sel(k, alg_sr, ZERO, r);
        let one = sel(k, alg_sr, ONE, r);
        let add = sel(k, alg_sr, ADD, r);
        let mul = sel(k, alg_sr, MUL, r);
        let add_assoc = sel(k, alg_sr, ADD_ASSOC, r);
        let add_comm = sel(k, alg_sr, ADD_COMM, r);
        let add_zero = sel(k, alg_sr, ADD_ZERO, r);
        let mul_assoc = sel(k, alg_sr, MUL_ASSOC, r);
        let mul_one_l = sel(k, alg_sr, MUL_ONE_L, r);
        let mul_one_r = sel(k, alg_sr, MUL_ONE_R, r);
        let distrib_l = sel(k, alg_sr, DISTRIB_L, r);
        let distrib_r = sel(k, alg_sr, DISTRIB_R, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let add_congr = build_binop_congr(k, lg, l1, carrier, add);
        let mul_congr = build_binop_congr(k, lg, l1, carrier, mul);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            zero,
            one,
            add,
            mul,
            add_congr,
            mul_congr,
            add_assoc,
            add_comm,
            add_zero,
            mul_assoc,
            mul_one_l,
            mul_one_r,
            distrib_l,
            distrib_r,
        ];
        declare_projection(k, algs_p, alg_sr, algs_sr, &args, R_FV)
    }

    /// `AlgS.Ring.ofAlg`.
    pub(crate) fn declare_ring_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_r: &RecordNames,
        algs_r: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_ONE_L, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO,
        };
        const R_FV: u64 = 21_270;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_r, CARRIER, r);
        let zero = sel(k, alg_r, ZERO, r);
        let one = sel(k, alg_r, ONE, r);
        let add = sel(k, alg_r, ADD, r);
        let mul = sel(k, alg_r, MUL, r);
        let add_assoc = sel(k, alg_r, ADD_ASSOC, r);
        let add_comm = sel(k, alg_r, ADD_COMM, r);
        let add_zero = sel(k, alg_r, ADD_ZERO, r);
        let mul_assoc = sel(k, alg_r, MUL_ASSOC, r);
        let mul_one_l = sel(k, alg_r, MUL_ONE_L, r);
        let mul_one_r = sel(k, alg_r, MUL_ONE_R, r);
        let distrib_l = sel(k, alg_r, DISTRIB_L, r);
        let distrib_r = sel(k, alg_r, DISTRIB_R, r);
        let neg = sel(k, alg_r, NEG, r);
        let neg_add = sel(k, alg_r, NEG_ADD, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let add_congr = build_binop_congr(k, lg, l1, carrier, add);
        let mul_congr = build_binop_congr(k, lg, l1, carrier, mul);
        let neg_congr = build_unop_congr(k, lg, l1, carrier, neg);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            zero,
            one,
            add,
            mul,
            add_congr,
            mul_congr,
            add_assoc,
            add_comm,
            add_zero,
            mul_assoc,
            mul_one_l,
            mul_one_r,
            distrib_l,
            distrib_r,
            neg,
            neg_congr,
            neg_add,
        ];
        declare_projection(k, algs_p, alg_r, algs_r, &args, R_FV)
    }

    /// `AlgS.CommRing.ofAlg` — the named example (`Int.commRing ->
    /// AlgS.CommRing`).
    pub(crate) fn declare_comm_ring_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_cr: &RecordNames,
        algs_cr: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::comm_ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_COMM, MUL_ONE_L, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO,
        };
        const R_FV: u64 = 21_280;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_cr, CARRIER, r);
        let zero = sel(k, alg_cr, ZERO, r);
        let one = sel(k, alg_cr, ONE, r);
        let add = sel(k, alg_cr, ADD, r);
        let mul = sel(k, alg_cr, MUL, r);
        let add_assoc = sel(k, alg_cr, ADD_ASSOC, r);
        let add_comm = sel(k, alg_cr, ADD_COMM, r);
        let add_zero = sel(k, alg_cr, ADD_ZERO, r);
        let mul_assoc = sel(k, alg_cr, MUL_ASSOC, r);
        let mul_one_l = sel(k, alg_cr, MUL_ONE_L, r);
        let mul_one_r = sel(k, alg_cr, MUL_ONE_R, r);
        let distrib_l = sel(k, alg_cr, DISTRIB_L, r);
        let distrib_r = sel(k, alg_cr, DISTRIB_R, r);
        let neg = sel(k, alg_cr, NEG, r);
        let neg_add = sel(k, alg_cr, NEG_ADD, r);
        let mul_comm = sel(k, alg_cr, MUL_COMM, r);
        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let add_congr = build_binop_congr(k, lg, l1, carrier, add);
        let mul_congr = build_binop_congr(k, lg, l1, carrier, mul);
        let neg_congr = build_unop_congr(k, lg, l1, carrier, neg);
        let args = vec![
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            zero,
            one,
            add,
            mul,
            add_congr,
            mul_congr,
            add_assoc,
            add_comm,
            add_zero,
            mul_assoc,
            mul_one_l,
            mul_one_r,
            distrib_l,
            distrib_r,
            neg,
            neg_congr,
            neg_add,
            mul_comm,
        ];
        declare_projection(k, algs_p, alg_cr, algs_cr, &args, R_FV)
    }
}

// ---------------------------------------------------------------------------
// Three generic theorems over `AlgS.Ring`.
// ---------------------------------------------------------------------------

/// Small app-chain helpers over an already-declared record's own equiv
/// infrastructure (values, not kernel primitives — see module doc).
fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

/// `AlgS.sub : forall (R:Ring), R.carrier -> R.carrier -> R.carrier :=
/// fun R a b => R.add a (R.neg b)`.
pub(crate) fn declare_sub_s(
    k: &mut Kernel,
    ring: &RecordNames,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    use idx::ring::{ADD, CARRIER, NEG};
    const R_FV: u64 = 21_300;
    const A_FV: u64 = 21_301;
    const B_FV: u64 = 21_302;
    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let add = sel(k, ring, ADD, r);
    let neg = sel(k, ring, NEG, r);
    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let nb = k.app(neg, b);
    let body = t_app(k, add, &[a, nb]);
    let value = lam_over(k, B_FV, carrier, body);
    let value = lam_over(k, A_FV, carrier, value);
    let ring_ty = k.const_(ring.ind, vec![]);
    let value = lam_over(k, R_FV, ring_ty, value);

    let ty_body = {
        let r2 = k.fvar(R_FV);
        let carrier2 = sel(k, ring, CARRIER, r2);
        let inner = arrow(k, carrier2, carrier2);
        arrow(k, carrier2, inner)
    };
    let ty = pi_over(k, R_FV, ring_ty, ty_body);

    let name = k.name_str(algs_p, "sub");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.sub_self : forall (R:Ring)(x:R.carrier), R.equiv (AlgS.sub R x x) R.zero`
/// — proved by `R.negAdd x` alone (the statement unfolds by beta+delta to
/// `R.equiv (R.add x (R.neg x)) R.zero`), matching `Alg.sub_self`'s own
/// discipline.
pub(crate) fn declare_sub_self(
    k: &mut Kernel,
    ring: &RecordNames,
    sub_name: NameId,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    use idx::ring::{CARRIER, EQUIV, NEG_ADD, ZERO};
    const R_FV: u64 = 21_310;
    const X_FV: u64 = 21_311;
    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let equiv = sel(k, ring, EQUIV, r);
    let zero = sel(k, ring, ZERO, r);
    let neg_add = sel(k, ring, NEG_ADD, r);
    let x = k.fvar(X_FV);
    let proof = k.app(neg_add, x);

    let sub_c = k.const_(sub_name, vec![]);
    let sub_r_x_x = t_app(k, sub_c, &[r, x, x]);
    let concl = app2(k, equiv, sub_r_x_x, zero);

    let value = proof;
    let value = lam_over(k, X_FV, carrier, value);
    let ring_ty = k.const_(ring.ind, vec![]);
    let value = lam_over(k, R_FV, ring_ty, value);

    let ty = pi_over(k, X_FV, carrier, concl);
    let ty = pi_over(k, R_FV, ring_ty, ty);

    let name = k.name_str(algs_p, "sub_self");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.neg_neg : forall (R:Ring)(a:R.carrier), R.equiv (R.neg (R.neg a)) a`.
///
/// Chain (5 `equivTrans` steps): `neg(neg a) -> add zero (neg(neg a)) ->
/// add (add a(neg a))(neg(neg a)) -> add a (add(neg a)(neg(neg a))) ->
/// add a zero -> a`, using `negAdd` at both `a` and `neg a`, `addComm`,
/// `addAssoc`, `addCongr`, `addZero`.
pub(crate) fn declare_neg_neg(
    k: &mut Kernel,
    ring: &RecordNames,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    use idx::ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_CONGR, ADD_ZERO, CARRIER, EQUIV, EQUIV_REFL, EQUIV_SYMM,
        EQUIV_TRANS, NEG, NEG_ADD, ZERO,
    };
    const R_FV: u64 = 21_320;
    const A_FV: u64 = 21_321;

    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let equiv = sel(k, ring, EQUIV, r);
    let equiv_refl = sel(k, ring, EQUIV_REFL, r);
    let equiv_symm = sel(k, ring, EQUIV_SYMM, r);
    let equiv_trans = sel(k, ring, EQUIV_TRANS, r);
    let add = sel(k, ring, ADD, r);
    let add_assoc = sel(k, ring, ADD_ASSOC, r);
    let add_comm = sel(k, ring, ADD_COMM, r);
    let add_zero = sel(k, ring, ADD_ZERO, r);
    let add_congr = sel(k, ring, ADD_CONGR, r);
    let neg = sel(k, ring, NEG, r);
    let neg_add = sel(k, ring, NEG_ADD, r);
    let zero = sel(k, ring, ZERO, r);

    let a = k.fvar(A_FV);
    let na = k.app(neg, a);
    let nna = k.app(neg, na);

    // negAdd(a) : equiv (add a (neg a)) zero
    let na_add = k.app(neg_add, a);
    let add_a_na = t_app(k, add, &[a, na]);
    // negAdd(neg a) : equiv (add (neg a) (neg(neg a))) zero
    let nna_add = k.app(neg_add, na);
    let add_na_nna = t_app(k, add, &[na, nna]);

    // addZeroLeft(w) : equiv (add zero w) w, via addComm(zero,w); addZero(w)
    let add_zero_left = |k: &mut Kernel, w: ExprId| -> (ExprId, ExprId) {
        // returns (proof, lhs=add zero w)
        let comm_zw = t_app(k, add_comm, &[zero, w]); // equiv (add zero w)(add w zero)
        let add_zero_w = t_app(k, add, &[zero, w]);
        let add_w_zero = t_app(k, add, &[w, zero]);
        let az_w = k.app(add_zero, w); // equiv (add w zero) w
        let combined = t_app(k, equiv_trans, &[add_zero_w, add_w_zero, w, comm_zw, az_w]);
        (combined, add_zero_w)
    };

    // step1 : equiv (neg(neg a)) (add zero (neg(neg a)))
    let (az_nna_proof, add_zero_nna) = add_zero_left(k, nna);
    let step1 = t_app(k, equiv_symm, &[add_zero_nna, nna, az_nna_proof]);

    // step2 : equiv (add zero (neg(neg a))) (add (add a (neg a)) (neg(neg a)))
    let zero_symm = t_app(k, equiv_symm, &[add_a_na, zero, na_add]); // equiv zero (add a (neg a))
    let refl_nna = t_app(k, equiv_refl, &[nna]);
    let add_ana_nna = t_app(k, add, &[add_a_na, nna]);
    let step2 = t_app(
        k,
        add_congr,
        &[zero, add_a_na, nna, nna, zero_symm, refl_nna],
    );

    // step3 : equiv (add (add a (neg a)) (neg(neg a))) (add a (add (neg a)(neg(neg a))))
    let add_a_addnna = t_app(k, add, &[a, add_na_nna]);
    let assoc_a_na_nna = t_app(k, add_assoc, &[a, na, nna]); // equiv (add(add a na)nna)(add a(add na nna))
    let step3 = assoc_a_na_nna;

    // step4 : equiv (add a (add(neg a)(neg(neg a)))) (add a zero)
    let add_a_zero = t_app(k, add, &[a, zero]);
    let refl_a = t_app(k, equiv_refl, &[a]);
    let step4 = t_app(k, add_congr, &[a, a, add_na_nna, zero, refl_a, nna_add]);

    // step5 : equiv (add a zero) a
    let step5 = k.app(add_zero, a);

    // Chain: nna -[step1]-> add_zero_nna -[step2]-> add_ana_nna -[step3]-> add_a_addnna -[step4]-> add_a_zero -[step5]-> a
    let c1 = t_app(
        k,
        equiv_trans,
        &[nna, add_zero_nna, add_ana_nna, step1, step2],
    );
    let c2 = t_app(k, equiv_trans, &[nna, add_ana_nna, add_a_addnna, c1, step3]);
    let c3 = t_app(k, equiv_trans, &[nna, add_a_addnna, add_a_zero, c2, step4]);
    let c4 = t_app(k, equiv_trans, &[nna, add_a_zero, a, c3, step5]);

    let value = c4;
    let value = lam_over(k, A_FV, carrier, value);
    let ring_ty = k.const_(ring.ind, vec![]);
    let value = lam_over(k, R_FV, ring_ty, value);

    let concl = app2(k, equiv, nna, a);
    let ty = pi_over(k, A_FV, carrier, concl);
    let ty = pi_over(k, R_FV, ring_ty, ty);

    let name = k.name_str(algs_p, "neg_neg");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.mul_zero : forall (R:Ring)(a:R.carrier), R.equiv (R.mul a R.zero) R.zero`.
///
/// Proved without the multiplicative identity, matching `Alg.ringMulZero`'s
/// own discipline. `x := mul a zero`; `equiv(x, add x x)` via `mulCongr` +
/// `distribL`; then the additive-group chain `zero -> add(neg x) x ->
/// add(neg x)(add x x) -> add(add(neg x)x)x -> add zero x -> x`, symm'd.
pub(crate) fn declare_mul_zero(
    k: &mut Kernel,
    ring: &RecordNames,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    use idx::ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_CONGR, ADD_ZERO, CARRIER, DISTRIB_L, EQUIV, EQUIV_REFL,
        EQUIV_SYMM, EQUIV_TRANS, MUL, MUL_CONGR, NEG, NEG_ADD, ZERO,
    };
    const R_FV: u64 = 21_330;
    const A_FV: u64 = 21_331;

    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let equiv = sel(k, ring, EQUIV, r);
    let equiv_refl = sel(k, ring, EQUIV_REFL, r);
    let equiv_symm = sel(k, ring, EQUIV_SYMM, r);
    let equiv_trans = sel(k, ring, EQUIV_TRANS, r);
    let add = sel(k, ring, ADD, r);
    let add_assoc = sel(k, ring, ADD_ASSOC, r);
    let add_comm = sel(k, ring, ADD_COMM, r);
    let add_zero = sel(k, ring, ADD_ZERO, r);
    let add_congr = sel(k, ring, ADD_CONGR, r);
    let mul = sel(k, ring, MUL, r);
    let mul_congr = sel(k, ring, MUL_CONGR, r);
    let distrib_l = sel(k, ring, DISTRIB_L, r);
    let neg = sel(k, ring, NEG, r);
    let neg_add = sel(k, ring, NEG_ADD, r);
    let zero = sel(k, ring, ZERO, r);

    let a = k.fvar(A_FV);
    let x = t_app(k, mul, &[a, zero]); // mul a zero
    let nx = k.app(neg, x);

    // z2 : equiv zero (add zero zero)
    let az_zero = k.app(add_zero, zero); // equiv (add zero zero) zero
    let add_zero_zero = t_app(k, add, &[zero, zero]);
    let z2 = t_app(k, equiv_symm, &[add_zero_zero, zero, az_zero]);

    // h2 : equiv (mul a zero) (mul a (add zero zero))
    let refl_a = t_app(k, equiv_refl, &[a]);
    let mul_a_azz = t_app(k, mul, &[a, add_zero_zero]);
    let h2 = t_app(k, mul_congr, &[a, a, zero, add_zero_zero, refl_a, z2]);

    // h3 : equiv (mul a (add zero zero)) (add x x)  [distribL a zero zero]
    let add_x_x = t_app(k, add, &[x, x]);
    let h3 = t_app(k, distrib_l, &[a, zero, zero]);

    // stepA : equiv x (add x x)
    let step_a = t_app(k, equiv_trans, &[x, mul_a_azz, add_x_x, h2, h3]);

    // negAddLeft(w) : equiv (add (neg w) w) zero, via addComm(neg w,w); negAdd(w)
    let neg_add_left = |k: &mut Kernel, w: ExprId, nw: ExprId| -> ExprId {
        let comm = t_app(k, add_comm, &[nw, w]); // equiv (add nw w)(add w nw)
        let add_nw_w = t_app(k, add, &[nw, w]);
        let add_w_nw = t_app(k, add, &[w, nw]);
        let na = k.app(neg_add, w); // equiv (add w nw) zero
        t_app(k, equiv_trans, &[add_nw_w, add_w_nw, zero, comm, na])
    };
    let neg_add_left_x = neg_add_left(k, x, nx);

    // step1 : equiv zero (add(neg x) x)
    let add_nx_x = t_app(k, add, &[nx, x]);
    let step1 = t_app(k, equiv_symm, &[add_nx_x, zero, neg_add_left_x]);

    // step2 : equiv (add(neg x) x) (add(neg x)(add x x))
    let refl_nx = t_app(k, equiv_refl, &[nx]);
    let add_nx_addxx = t_app(k, add, &[nx, add_x_x]);
    let step2 = t_app(k, add_congr, &[nx, nx, x, add_x_x, refl_nx, step_a]);

    // step3 : equiv (add(neg x)(add x x)) (add(add(neg x)x)x)  [symm addAssoc(nx,x,x)]
    let assoc_nx_x_x = t_app(k, add_assoc, &[nx, x, x]); // equiv (add(add nx x)x)(add nx(add x x))
    let add_addnxx_x = t_app(k, add, &[add_nx_x, x]);
    let step3 = t_app(k, equiv_symm, &[add_addnxx_x, add_nx_addxx, assoc_nx_x_x]);

    // step4 : equiv (add(add(neg x)x)x) (add zero x)
    let refl_x = t_app(k, equiv_refl, &[x]);
    let add_zero_x = t_app(k, add, &[zero, x]);
    let step4 = t_app(
        k,
        add_congr,
        &[add_nx_x, zero, x, x, neg_add_left_x, refl_x],
    );

    // step5 : equiv (add zero x) x  [addComm(zero,x); addZero(x)]
    let comm_zx = t_app(k, add_comm, &[zero, x]);
    let az_x = k.app(add_zero, x);
    let add_x_zero = t_app(k, add, &[x, zero]);
    let step5 = t_app(k, equiv_trans, &[add_zero_x, add_x_zero, x, comm_zx, az_x]);

    // chain: zero -[step1]-> add_nx_x -[step2]-> add_nx_addxx -[step3]-> add_addnxx_x -[step4]-> add_zero_x -[step5]-> x
    let c1 = t_app(
        k,
        equiv_trans,
        &[zero, add_nx_x, add_nx_addxx, step1, step2],
    );
    let c2 = t_app(
        k,
        equiv_trans,
        &[zero, add_nx_addxx, add_addnxx_x, c1, step3],
    );
    let c3 = t_app(k, equiv_trans, &[zero, add_addnxx_x, add_zero_x, c2, step4]);
    let c4 = t_app(k, equiv_trans, &[zero, add_zero_x, x, c3, step5]);
    // c4 : equiv zero x -- symm to get equiv x zero
    let result = t_app(k, equiv_symm, &[zero, x, c4]);

    let value = result;
    let value = lam_over(k, A_FV, carrier, value);
    let ring_ty = k.const_(ring.ind, vec![]);
    let value = lam_over(k, R_FV, ring_ty, value);

    let concl = app2(k, equiv, x, zero);
    let ty = pi_over(k, A_FV, carrier, concl);
    let ty = pi_over(k, R_FV, ring_ty, ty);

    let name = k.name_str(algs_p, "mul_zero");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.mul_neg_one : forall (R:Ring)(x:R.carrier), R.equiv (R.mul x
/// (R.neg R.one)) (R.neg x)` -- ADR-1590, over `AlgS.Ring`, the setoid twin
/// of `Alg.mul_neg_one` (ADR-1584).
///
/// Proof (10 `equivTrans` steps, none using a Group-level uniqueness
/// theorem -- `AlgS` has none over `Group`, only over `Ring`, so this stays
/// self-contained within the ring calculus, matching `mul_zero`/`neg_neg`'s
/// own discipline):
///
/// `h : equiv (add y x) zero`, where `y := mul x (neg one)`, derived from
/// `distribL x (neg one) one` + the ALREADY-DECLARED `AlgS.mul_zero` (reused
/// by name, not reproved) + `mulOneR x`: `mul x (add (neg one) one) ~ mul x
/// zero ~ zero` (via `mulCongr` on `addComm(neg one,one)`+`negAdd(one)`,
/// then `mul_zero`), and `mul x (add(neg one)one) ~ add y (mul x one)` (via
/// `distribL`), so `add y (mul x one) ~ zero`; congr-substituting `mul x
/// one ~> x` via `mulOneR` gives `h`.
///
/// Then the standard "both are additive inverses of x" chain: `y -> add y
/// zero -> add y (add x (neg x)) -> add (add y x) (neg x) -> add zero (neg
/// x) -> neg x`, using `h` at the third step.
#[allow(clippy::too_many_lines)]
pub(crate) fn declare_mul_neg_one(
    k: &mut Kernel,
    ring: &RecordNames,
    mul_zero_name: NameId,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    use idx::ring::{
        ADD, ADD_ASSOC, ADD_COMM, ADD_CONGR, ADD_ZERO, CARRIER, DISTRIB_L, EQUIV, EQUIV_REFL,
        EQUIV_SYMM, EQUIV_TRANS, MUL, MUL_CONGR, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO,
    };
    const R_FV: u64 = 21_350;
    const X_FV: u64 = 21_351;

    let r = k.fvar(R_FV);
    let carrier = sel(k, ring, CARRIER, r);
    let equiv = sel(k, ring, EQUIV, r);
    let equiv_refl = sel(k, ring, EQUIV_REFL, r);
    let equiv_symm = sel(k, ring, EQUIV_SYMM, r);
    let equiv_trans = sel(k, ring, EQUIV_TRANS, r);
    let add = sel(k, ring, ADD, r);
    let add_assoc = sel(k, ring, ADD_ASSOC, r);
    let add_comm = sel(k, ring, ADD_COMM, r);
    let add_zero = sel(k, ring, ADD_ZERO, r);
    let add_congr = sel(k, ring, ADD_CONGR, r);
    let mul = sel(k, ring, MUL, r);
    let mul_congr = sel(k, ring, MUL_CONGR, r);
    let mul_one_r = sel(k, ring, MUL_ONE_R, r);
    let distrib_l = sel(k, ring, DISTRIB_L, r);
    let neg = sel(k, ring, NEG, r);
    let neg_add = sel(k, ring, NEG_ADD, r);
    let one = sel(k, ring, ONE, r);
    let zero = sel(k, ring, ZERO, r);

    let x = k.fvar(X_FV);
    let neg_one = k.app(neg, one);
    let neg_x = k.app(neg, x);
    let y = t_app(k, mul, &[x, neg_one]); // y := mul x (neg one)

    // stepA : equiv (add (neg one) one) zero
    let add_no_o = t_app(k, add, &[neg_one, one]);
    let add_o_no = t_app(k, add, &[one, neg_one]);
    let comm_no_o = t_app(k, add_comm, &[neg_one, one]);
    let na_one = k.app(neg_add, one); // equiv (add one (neg one)) zero
    let step_a = t_app(
        k,
        equiv_trans,
        &[add_no_o, add_o_no, zero, comm_no_o, na_one],
    );

    // h2 : equiv (mul x (add (neg one) one)) (mul x zero)
    let refl_x = t_app(k, equiv_refl, &[x]);
    let mul_x_addnoo = t_app(k, mul, &[x, add_no_o]);
    let mul_x_zero = t_app(k, mul, &[x, zero]);
    let h2 = t_app(k, mul_congr, &[x, x, add_no_o, zero, refl_x, step_a]);

    // mz : equiv (mul x zero) zero  -- the already-declared AlgS.mul_zero.
    let mul_zero_c = k.const_(mul_zero_name, vec![]);
    let mz = t_app(k, mul_zero_c, &[r, x]);

    // step_d : equiv (mul x (add (neg one) one)) zero
    let step_d = t_app(k, equiv_trans, &[mul_x_addnoo, mul_x_zero, zero, h2, mz]);

    // distrib : equiv (mul x (add (neg one) one)) (add y (mul x one))
    let mul_x_one = t_app(k, mul, &[x, one]);
    let add_y_mxo = t_app(k, add, &[y, mul_x_one]);
    let distrib = t_app(k, distrib_l, &[x, neg_one, one]);

    // h_raw : equiv (add y (mul x one)) zero
    let step_f = t_app(k, equiv_symm, &[mul_x_addnoo, add_y_mxo, distrib]);
    let h_raw = t_app(
        k,
        equiv_trans,
        &[add_y_mxo, mul_x_addnoo, zero, step_f, step_d],
    );

    // h : equiv (add y x) zero
    let mo_r = k.app(mul_one_r, x); // equiv (mul x one) x
    let symm_mo_r = t_app(k, equiv_symm, &[mul_x_one, x, mo_r]); // equiv x (mul x one)
    let refl_y = t_app(k, equiv_refl, &[y]);
    let add_y_x = t_app(k, add, &[y, x]);
    let addcongr_step = t_app(k, add_congr, &[y, y, x, mul_x_one, refl_y, symm_mo_r]); // equiv (add y x) (add y (mul x one))
    let h = t_app(
        k,
        equiv_trans,
        &[add_y_x, add_y_mxo, zero, addcongr_step, h_raw],
    );

    // Final chain: y -> add y zero -> add y (add x (neg x)) -> add (add y x) (neg x)
    //           -> add zero (neg x) -> neg x
    let az_y = k.app(add_zero, y); // equiv (add y zero) y
    let add_y_zero = t_app(k, add, &[y, zero]);
    let r0 = t_app(k, equiv_symm, &[add_y_zero, y, az_y]); // equiv y (add y zero)

    let na_x = k.app(neg_add, x); // equiv (add x (neg x)) zero
    let add_x_negx = t_app(k, add, &[x, neg_x]);
    let symm_na_x = t_app(k, equiv_symm, &[add_x_negx, zero, na_x]); // equiv zero (add x (neg x))
    let add_y_addxnegx = t_app(k, add, &[y, add_x_negx]);
    let r1 = t_app(k, add_congr, &[y, y, zero, add_x_negx, refl_y, symm_na_x]); // equiv (add y zero) (add y (add x (neg x)))

    let assoc_yxnegx = t_app(k, add_assoc, &[y, x, neg_x]); // equiv (add(add y x)negx)(add y(add x negx))
    let add_addyx_negx = t_app(k, add, &[add_y_x, neg_x]);
    let r2 = t_app(
        k,
        equiv_symm,
        &[add_addyx_negx, add_y_addxnegx, assoc_yxnegx],
    ); // equiv (add y (add x (neg x))) (add (add y x) (neg x))

    let refl_negx = t_app(k, equiv_refl, &[neg_x]);
    let add_zero_negx = t_app(k, add, &[zero, neg_x]);
    let r3 = t_app(k, add_congr, &[add_y_x, zero, neg_x, neg_x, h, refl_negx]); // equiv (add (add y x) (neg x)) (add zero (neg x))

    // r4 : equiv (add zero (neg x)) (neg x)  [addComm(zero,negx); addZero(negx)]
    let comm_zero_negx = t_app(k, add_comm, &[zero, neg_x]);
    let add_negx_zero = t_app(k, add, &[neg_x, zero]);
    let az_negx = k.app(add_zero, neg_x);
    let r4 = t_app(
        k,
        equiv_trans,
        &[add_zero_negx, add_negx_zero, neg_x, comm_zero_negx, az_negx],
    );

    let c1 = t_app(k, equiv_trans, &[y, add_y_zero, add_y_addxnegx, r0, r1]);
    let c2 = t_app(k, equiv_trans, &[y, add_y_addxnegx, add_addyx_negx, c1, r2]);
    let c3 = t_app(k, equiv_trans, &[y, add_addyx_negx, add_zero_negx, c2, r3]);
    let result = t_app(k, equiv_trans, &[y, add_zero_negx, neg_x, c3, r4]);

    let value = result;
    let value = lam_over(k, X_FV, carrier, value);
    let ring_ty = k.const_(ring.ind, vec![]);
    let value = lam_over(k, R_FV, ring_ty, value);

    let concl = app2(k, equiv, y, neg_x);
    let ty = pi_over(k, X_FV, carrier, concl);
    let ty = pi_over(k, R_FV, ring_ty, ty);

    let name = k.name_str(algs_p, "mul_neg_one");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.add_left_cancel : forall (G:Group)(a b c:G.carrier), G.equiv
/// (G.op a b) (G.op a c) -> G.equiv b c` -- ADR-1590, the setoid twin of
/// `nat_prelude::structures::build_mul_left_cancel_generic` (`Alg.
/// mul_left_cancel`), over `AlgS.Group` -- ported step for step, `Eq.trans`/
/// `symm_of`/`congr_arg` replaced by `equivTrans`/`equivSymm`/`opCongr`.
#[allow(clippy::too_many_lines)]
pub(crate) fn declare_add_left_cancel(
    k: &mut Kernel,
    group: &RecordNames,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    use idx::group::{
        ASSOC, CARRIER, E, EQUIV, EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, IDENT_L, INV, INV_L, OP,
        OP_CONGR,
    };
    const G_FV: u64 = 21_360;
    const A_FV: u64 = 21_361;
    const B_FV: u64 = 21_362;
    const C_FV: u64 = 21_363;
    const H_FV: u64 = 21_364;

    let g = k.fvar(G_FV);
    let carrier = sel(k, group, CARRIER, g);
    let equiv = sel(k, group, EQUIV, g);
    let equiv_refl = sel(k, group, EQUIV_REFL, g);
    let equiv_symm = sel(k, group, EQUIV_SYMM, g);
    let equiv_trans = sel(k, group, EQUIV_TRANS, g);
    let op = sel(k, group, OP, g);
    let op_congr = sel(k, group, OP_CONGR, g);
    let e = sel(k, group, E, g);
    let inv = sel(k, group, INV, g);
    let ident_l = sel(k, group, IDENT_L, g);
    let inv_l = sel(k, group, INV_L, g);
    let assoc = sel(k, group, ASSOC, g);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let inv_a = k.app(inv, a);

    let op_a_b = t_app(k, op, &[a, b]);
    let op_a_c = t_app(k, op, &[a, c]);
    let hyp_ty = app2(k, equiv, op_a_b, op_a_c);
    let h = k.fvar(H_FV);

    // r0 : equiv b (op e b)
    let op_e_b = t_app(k, op, &[e, b]);
    let ident_l_b = k.app(ident_l, b); // equiv (op e b) b
    let r0 = t_app(k, equiv_symm, &[op_e_b, b, ident_l_b]);

    // r1 : equiv (op e b) (op (op inv_a a) b)
    let inv_l_a = k.app(inv_l, a); // equiv (op inv_a a) e
    let op_invaa = t_app(k, op, &[inv_a, a]);
    let symm_inv_l_a = t_app(k, equiv_symm, &[op_invaa, e, inv_l_a]); // equiv e (op inv_a a)
    let op_invaa_b = t_app(k, op, &[op_invaa, b]);
    let refl_b = t_app(k, equiv_refl, &[b]);
    let r1 = t_app(k, op_congr, &[e, op_invaa, b, b, symm_inv_l_a, refl_b]);

    // r2 : equiv (op (op inv_a a) b) (op inv_a (op a b))
    let op_inva_opab = t_app(k, op, &[inv_a, op_a_b]);
    let r2 = t_app(k, assoc, &[inv_a, a, b]);

    // r3 : equiv (op inv_a (op a b)) (op inv_a (op a c))
    let op_inva_opac = t_app(k, op, &[inv_a, op_a_c]);
    let refl_inva = t_app(k, equiv_refl, &[inv_a]);
    let r3 = t_app(k, op_congr, &[inv_a, inv_a, op_a_b, op_a_c, refl_inva, h]);

    // r4 : equiv (op inv_a (op a c)) (op (op inv_a a) c)
    let op_invaa_c = t_app(k, op, &[op_invaa, c]);
    let assoc_invaac = t_app(k, assoc, &[inv_a, a, c]);
    let r4 = t_app(k, equiv_symm, &[op_invaa_c, op_inva_opac, assoc_invaac]);

    // r5 : equiv (op (op inv_a a) c) (op e c)
    let op_e_c = t_app(k, op, &[e, c]);
    let refl_c = t_app(k, equiv_refl, &[c]);
    let r5 = t_app(k, op_congr, &[op_invaa, e, c, c, inv_l_a, refl_c]);

    // r6 : equiv (op e c) c
    let r6 = k.app(ident_l, c);

    let step1 = t_app(k, equiv_trans, &[b, op_e_b, op_invaa_b, r0, r1]);
    let step2 = t_app(k, equiv_trans, &[b, op_invaa_b, op_inva_opab, step1, r2]);
    let step3 = t_app(k, equiv_trans, &[b, op_inva_opab, op_inva_opac, step2, r3]);
    let step4 = t_app(k, equiv_trans, &[b, op_inva_opac, op_invaa_c, step3, r4]);
    let step5 = t_app(k, equiv_trans, &[b, op_invaa_c, op_e_c, step4, r5]);
    let result = t_app(k, equiv_trans, &[b, op_e_c, c, step5, r6]);

    let value = lam_over(k, H_FV, hyp_ty, result);
    let value = lam_over(k, C_FV, carrier, value);
    let value = lam_over(k, B_FV, carrier, value);
    let value = lam_over(k, A_FV, carrier, value);
    let group_ty = k.const_(group.ind, vec![]);
    let value = lam_over(k, G_FV, group_ty, value);

    let concl = app2(k, equiv, b, c);
    let ty = pi_over(k, H_FV, hyp_ty, concl);
    let ty = pi_over(k, C_FV, carrier, ty);
    let ty = pi_over(k, B_FV, carrier, ty);
    let ty = pi_over(k, A_FV, carrier, ty);
    let ty = pi_over(k, G_FV, group_ty, ty);

    let name = k.name_str(algs_p, "add_left_cancel");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// Assembly: declare everything, in build order.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuresSExtraNames {
    pub comm_ring_to_ring_s: NameId,
    pub magma_ofalg: NameId,
    pub semigroup_ofalg: NameId,
    pub monoid_ofalg: NameId,
    pub comm_monoid_ofalg: NameId,
    pub group_ofalg: NameId,
    pub comm_group_ofalg: NameId,
    pub semiring_ofalg: NameId,
    pub ring_ofalg: NameId,
    pub comm_ring_ofalg: NameId,
    pub sub: NameId,
    pub sub_self: NameId,
    pub neg_neg: NameId,
    pub mul_zero: NameId,
    pub mul_neg_one: NameId,
    pub add_left_cancel: NameId,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn declare_structures_s_extra(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: &StructuresSNames,
    st: &StructuresSRecordNames,
    alg_p: &structures::StructuresPrelude,
    alg_st: &structures::StructuresNames,
) -> Result<StructuresSExtraNames, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let comm_ring_to_ring_s = declare_comm_ring_to_ring_s(k, st, p)?;

    let magma_ofalg = ofalg::declare_magma_ofalg(k, lg, l1, &alg_st.magma, &st.magma, p.magma)?;
    let semigroup_ofalg =
        ofalg::declare_semigroup_ofalg(k, lg, l1, &alg_st.semigroup, &st.semigroup, p.semigroup)?;
    let monoid_ofalg =
        ofalg::declare_monoid_ofalg(k, lg, l1, &alg_st.monoid, &st.monoid, p.monoid)?;
    let comm_monoid_ofalg = ofalg::declare_comm_monoid_ofalg(
        k,
        lg,
        l1,
        &alg_st.comm_monoid,
        &st.comm_monoid,
        p.comm_monoid,
    )?;
    let group_ofalg = ofalg::declare_group_ofalg(k, lg, l1, &alg_st.group, &st.group, p.group)?;
    let comm_group_ofalg = ofalg::declare_comm_group_ofalg(
        k,
        lg,
        l1,
        &alg_st.comm_group,
        &st.comm_group,
        p.comm_group,
    )?;
    let semiring_ofalg =
        ofalg::declare_semiring_ofalg(k, lg, l1, &alg_st.semiring, &st.semiring, p.semiring)?;
    let ring_ofalg = ofalg::declare_ring_ofalg(k, lg, l1, &alg_st.ring, &st.ring, p.ring)?;
    let comm_ring_ofalg =
        ofalg::declare_comm_ring_ofalg(k, lg, l1, &alg_st.comm_ring, &st.comm_ring, p.comm_ring)?;

    let sub = declare_sub_s(k, &st.ring, p.algs)?;
    let sub_self = declare_sub_self(k, &st.ring, sub, p.algs)?;
    let neg_neg = declare_neg_neg(k, &st.ring, p.algs)?;
    let mul_zero = declare_mul_zero(k, &st.ring, p.algs)?;
    let mul_neg_one = declare_mul_neg_one(k, &st.ring, mul_zero, p.algs)?;
    let add_left_cancel = declare_add_left_cancel(k, &st.group, p.algs)?;

    let _ = alg_p;

    Ok(StructuresSExtraNames {
        comm_ring_to_ring_s,
        magma_ofalg,
        semigroup_ofalg,
        monoid_ofalg,
        comm_monoid_ofalg,
        group_ofalg,
        comm_group_ofalg,
        semiring_ofalg,
        ring_ofalg,
        comm_ring_ofalg,
        sub,
        sub_self,
        neg_neg,
        mul_zero,
        mul_neg_one,
        add_left_cancel,
    })
}

#[cfg(test)]
mod structures_setoid_tests {
    use super::*;
    use crate::build_logic_prelude;
    use crate::nat_prelude::structures as algeq;

    fn build_both_spines(
        k: &mut Kernel,
    ) -> (
        LogicPrelude,
        StructuresSNames,
        StructuresSRecordNames,
        algeq::StructuresPrelude,
        algeq::StructuresNames,
    ) {
        let logic = build_logic_prelude(k).expect("logic prelude must build");
        let alg_p = algeq::intern_structures_names(k);
        let alg_st = algeq::declare_structures_all(k, &alg_p, &logic).expect("Alg spine builds");
        let p = intern_structures_s_names(k);
        let st = declare_structures_s_all(k, &p, &logic).expect("AlgS spine builds");
        (logic, p, st, alg_p, alg_st)
    }

    #[test]
    fn every_records_field_count_matches_the_design() {
        let mut k = Kernel::new();
        let (_logic, _p, st, _alg_p, _alg_st) = build_both_spines(&mut k);
        let expected: &[(&str, usize)] = &[
            ("Magma", 7),
            ("Semigroup", 8),
            ("Monoid", 11),
            ("CommMonoid", 12),
            ("Group", 15),
            ("CommGroup", 16),
            ("Semiring", 19),
            ("Ring", 22),
            ("CommRing", 23),
        ];
        let actual = [
            st.magma.field_count(),
            st.semigroup.field_count(),
            st.monoid.field_count(),
            st.comm_monoid.field_count(),
            st.group.field_count(),
            st.comm_group.field_count(),
            st.semiring.field_count(),
            st.ring.field_count(),
            st.comm_ring.field_count(),
        ];
        for (i, (name, want)) in expected.iter().enumerate() {
            assert_eq!(actual[i], *want, "{name} field count");
        }
    }

    #[test]
    fn every_record_declaration_is_present_in_the_environment() {
        let mut k = Kernel::new();
        let (_logic, _p, st, _alg_p, _alg_st) = build_both_spines(&mut k);
        for rn in [
            &st.magma,
            &st.semigroup,
            &st.monoid,
            &st.comm_monoid,
            &st.group,
            &st.comm_group,
            &st.semiring,
            &st.ring,
            &st.comm_ring,
        ] {
            assert!(k.environment().get(rn.ind).is_some(), "inductive missing");
            assert!(k.environment().get(rn.rec).is_some(), "recursor missing");
            for i in 0..rn.field_count() {
                assert!(
                    k.environment().get(rn.sel(i)).is_some(),
                    "selector {i} missing"
                );
            }
        }
    }

    #[test]
    fn ofalg_and_generic_theorems_all_admit() {
        let mut k = Kernel::new();
        let (logic, p, st, alg_p, alg_st) = build_both_spines(&mut k);
        let extra = declare_structures_s_extra(&mut k, &logic, &p, &st, &alg_p, &alg_st)
            .expect("ofAlg projections and generic theorems must admit");
        for name in [
            extra.comm_ring_to_ring_s,
            extra.magma_ofalg,
            extra.semigroup_ofalg,
            extra.monoid_ofalg,
            extra.comm_monoid_ofalg,
            extra.group_ofalg,
            extra.comm_group_ofalg,
            extra.semiring_ofalg,
            extra.ring_ofalg,
            extra.comm_ring_ofalg,
            extra.sub,
            extra.sub_self,
            extra.neg_neg,
            extra.mul_zero,
            extra.mul_neg_one,
            extra.add_left_cancel,
        ] {
            assert!(k.environment().get(name).is_some());
        }
    }

    /// Every `AlgS.*` extra declaration (projections, `sub`/`sub_self`, and
    /// the two generic theorems) must have an empty axiom footprint.
    #[test]
    fn ofalg_and_generic_theorems_are_axiom_free() {
        let mut k = Kernel::new();
        let (logic, p, st, alg_p, alg_st) = build_both_spines(&mut k);
        let extra = declare_structures_s_extra(&mut k, &logic, &p, &st, &alg_p, &alg_st)
            .expect("ofAlg projections and generic theorems must admit");
        for name in [
            extra.comm_ring_to_ring_s,
            extra.magma_ofalg,
            extra.semigroup_ofalg,
            extra.monoid_ofalg,
            extra.comm_monoid_ofalg,
            extra.group_ofalg,
            extra.comm_group_ofalg,
            extra.semiring_ofalg,
            extra.ring_ofalg,
            extra.comm_ring_ofalg,
            extra.sub,
            extra.sub_self,
            extra.neg_neg,
            extra.mul_zero,
            extra.mul_neg_one,
            extra.add_left_cancel,
        ] {
            assert!(
                k.axiom_footprint(name).is_empty(),
                "declaration must have an empty axiom footprint"
            );
        }
    }

    /// Evaluation test (deliverable 3): projecting `Int.commRing` through
    /// `AlgS.CommRing.ofAlg` and reading back `mulComm`'s type by
    /// REDUCTION must be `def_eq` to `Int.mul_comm`'s own rendered type.
    #[test]
    fn int_comm_ring_ofalg_mul_comm_matches_int_mul_comm_type() {
        use crate::rat_prelude::build_rat_prelude;
        use idx::comm_ring::MUL_COMM;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let st = np.structures_s;
        let extra = np.structures_s_extra;

        let int_comm_ring = k.const_(rp.algebra.int_comm_ring, vec![]);
        let ofalg_c = k.const_(extra.comm_ring_ofalg, vec![]);
        let projected = k.app(ofalg_c, int_comm_ring);

        let mul_comm_sel = k.const_(st.comm_ring.sel(MUL_COMM), vec![]);
        let projected_mul_comm = k.app(mul_comm_sel, projected);

        let projected_ty = k
            .infer(projected_mul_comm)
            .expect("projected mulComm must infer a type");

        let int_mul_comm = k.const_(rp.int.mul_comm, vec![]);
        let int_mul_comm_ty = k
            .infer(int_mul_comm)
            .expect("Int.mul_comm must infer a type");

        assert!(
            k.def_eq(projected_ty, int_mul_comm_ty),
            "AlgS.CommRing.ofAlg(Int.commRing).mulComm's type must be def_eq to Int.mul_comm's own type"
        );
    }

    /// Deliverable 5: `AlgS.mul_zero` instantiated at ℤ THROUGH `ofAlg`
    /// (`AlgS.Ring.ofAlg(Int.ring)`), concrete (`Int.zero`) AND symbolic (a
    /// closed universally-quantified lambda, the same "close over a bound
    /// `a` via `lam_over`" technique `rat_prelude::algebra_instances`'s own
    /// `ring_mul_zero_applies_at_int_and_rat_instances` uses) -- and,
    /// symbolically, `def_eq` to `Int.mul_zero`'s own type.
    #[test]
    fn mul_zero_instantiated_at_int_through_ofalg_concrete_and_symbolic() {
        use crate::rat_prelude::build_rat_prelude;
        const A_FV: u64 = 24_000;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;

        let int_ring_alg = k.const_(rp.algebra.int_ring, vec![]);
        let ring_ofalg = k.const_(extra.ring_ofalg, vec![]);
        let int_ring_s = k.app(ring_ofalg, int_ring_alg);
        let mul_zero_c = k.const_(extra.mul_zero, vec![]);
        let applied = k.app(mul_zero_c, int_ring_s);
        let int_ty = k.const_(rp.int.z, vec![]);

        // Concrete: at Int.zero.
        let zero_c = k.const_(rp.int.zero, vec![]);
        let applied_zero = k.app(applied, zero_c);
        assert!(
            k.infer(applied_zero).is_ok(),
            "AlgS.mul_zero applied at Int's Ring projection must infer a type at Int.zero"
        );

        // Symbolic: closed over a bound `a`.
        let a = k.fvar(A_FV);
        let applied_a = k.app(applied, a);
        let closed = lam_over(&mut k, A_FV, int_ty, applied_a);
        let ty = k
            .infer(closed)
            .expect("AlgS.mul_zero closed at Int's Ring projection must infer a type");

        let int_mul_zero = k.const_(rp.int.mul_zero, vec![]);
        let int_mul_zero_closed = {
            let a2 = k.fvar(A_FV);
            let applied2 = k.app(int_mul_zero, a2);
            lam_over(&mut k, A_FV, int_ty, applied2)
        };
        let int_mul_zero_ty = k
            .infer(int_mul_zero_closed)
            .expect("Int.mul_zero closed must infer a type");
        assert!(
            k.def_eq(ty, int_mul_zero_ty),
            "AlgS.mul_zero(AlgS.Ring.ofAlg(Int.ring)) must be def_eq to Int.mul_zero at a free `a`"
        );
    }

    /// Deliverable 5: `AlgS.neg_neg` instantiated at ℤ through `ofAlg`,
    /// concrete and symbolic. Int has no named `neg_neg` theorem (ADR-1587
    /// §4: only a private helper in `int_prelude/gcd.rs`), so this test
    /// confirms only well-typedness, like `CReal`'s own.
    #[test]
    fn neg_neg_instantiated_at_int_through_ofalg_concrete_and_symbolic() {
        use crate::rat_prelude::build_rat_prelude;
        const A_FV: u64 = 24_010;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;

        let int_ring_alg = k.const_(rp.algebra.int_ring, vec![]);
        let ring_ofalg = k.const_(extra.ring_ofalg, vec![]);
        let int_ring_s = k.app(ring_ofalg, int_ring_alg);
        let neg_neg_c = k.const_(extra.neg_neg, vec![]);
        let applied = k.app(neg_neg_c, int_ring_s);
        let int_ty = k.const_(rp.int.z, vec![]);

        let zero_c = k.const_(rp.int.zero, vec![]);
        let applied_zero = k.app(applied, zero_c);
        assert!(
            k.infer(applied_zero).is_ok(),
            "AlgS.neg_neg applied at Int's Ring projection must infer a type at Int.zero"
        );

        let a = k.fvar(A_FV);
        let applied_a = k.app(applied, a);
        let closed = lam_over(&mut k, A_FV, int_ty, applied_a);
        assert!(
            k.infer(closed).is_ok(),
            "AlgS.neg_neg closed at Int's Ring projection must infer a type"
        );
    }

    /// Deliverable 5: `AlgS.sub_self` instantiated at ℤ through `ofAlg`,
    /// concrete and symbolic.
    #[test]
    fn sub_self_instantiated_at_int_through_ofalg_concrete_and_symbolic() {
        use crate::rat_prelude::build_rat_prelude;
        const A_FV: u64 = 24_020;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;

        let int_ring_alg = k.const_(rp.algebra.int_ring, vec![]);
        let ring_ofalg = k.const_(extra.ring_ofalg, vec![]);
        let int_ring_s = k.app(ring_ofalg, int_ring_alg);
        let sub_self_c = k.const_(extra.sub_self, vec![]);
        let applied = k.app(sub_self_c, int_ring_s);
        let int_ty = k.const_(rp.int.z, vec![]);

        let zero_c = k.const_(rp.int.zero, vec![]);
        let applied_zero = k.app(applied, zero_c);
        assert!(
            k.infer(applied_zero).is_ok(),
            "AlgS.sub_self applied at Int's Ring projection must infer a type at Int.zero"
        );

        let a = k.fvar(A_FV);
        let applied_a = k.app(applied, a);
        let closed = lam_over(&mut k, A_FV, int_ty, applied_a);
        assert!(
            k.infer(closed).is_ok(),
            "AlgS.sub_self closed at Int's Ring projection must infer a type"
        );
    }

    /// Deliverable 5 (ADR-1590): `AlgS.mul_neg_one` instantiated at ℤ
    /// through `ofAlg`, concrete (`Int.zero`) and symbolic. `Int.neg_one_
    /// mul` is the MIRRORED LEFT form (ADR-1584 §3: bridging needs
    /// `mul_comm`, which this theorem is deliberately stated without), so
    /// there is no retirement target here -- well-typedness only, like
    /// `neg_neg`'s own Int control.
    #[test]
    fn mul_neg_one_instantiated_at_int_through_ofalg_concrete_and_symbolic() {
        use crate::rat_prelude::build_rat_prelude;
        const A_FV: u64 = 24_030;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;

        let int_ring_alg = k.const_(rp.algebra.int_ring, vec![]);
        let ring_ofalg = k.const_(extra.ring_ofalg, vec![]);
        let int_ring_s = k.app(ring_ofalg, int_ring_alg);
        let mul_neg_one_c = k.const_(extra.mul_neg_one, vec![]);
        let applied = k.app(mul_neg_one_c, int_ring_s);
        let int_ty = k.const_(rp.int.z, vec![]);

        let zero_c = k.const_(rp.int.zero, vec![]);
        let applied_zero = k.app(applied, zero_c);
        assert!(
            k.infer(applied_zero).is_ok(),
            "AlgS.mul_neg_one applied at Int's Ring projection must infer a type at Int.zero"
        );

        let a = k.fvar(A_FV);
        let applied_a = k.app(applied, a);
        let closed = lam_over(&mut k, A_FV, int_ty, applied_a);
        assert!(
            k.infer(closed).is_ok(),
            "AlgS.mul_neg_one closed at Int's Ring projection must infer a type"
        );
    }

    /// Deliverable 5 (ADR-1590): `AlgS.add_left_cancel` instantiated at ℤ
    /// through `ofAlg` (`AlgS.Group.ofAlg(Int.addGroup)`), closed over
    /// `(a,b,c)` (the hypothesis left implicit in the returned arrow type,
    /// mirroring `retirement_int_add_left_cancel`'s own technique), is
    /// `def_eq` to `Int.add_left_cancel`'s own declared type -- the SAME
    /// carrier theorem `Alg.mul_left_cancel` (ADR-1587) already retired to,
    /// now reached from the setoid spine too.
    #[test]
    fn add_left_cancel_instantiated_at_int_through_ofalg_matches_int_add_left_cancel_type() {
        use crate::rat_prelude::build_rat_prelude;
        const A_FV: u64 = 24_040;
        const B_FV: u64 = 24_041;
        const C_FV: u64 = 24_042;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;

        let int_add_group_alg = k.const_(rp.algebra.int_add_group, vec![]);
        let group_ofalg = k.const_(extra.group_ofalg, vec![]);
        let int_group_s = k.app(group_ofalg, int_add_group_alg);
        let add_left_cancel_c = k.const_(extra.add_left_cancel, vec![]);
        let int_ty = k.const_(rp.int.z, vec![]);

        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let c = k.fvar(C_FV);
        let generic_applied = {
            let e1 = k.app(add_left_cancel_c, int_group_s);
            let e2 = k.app(e1, a);
            let e3 = k.app(e2, b);
            k.app(e3, c)
        };
        let generic_closed = {
            let v = generic_applied;
            let v = lam_over(&mut k, C_FV, int_ty, v);
            let v = lam_over(&mut k, B_FV, int_ty, v);
            lam_over(&mut k, A_FV, int_ty, v)
        };
        let generic_ty = k
            .infer(generic_closed)
            .expect("AlgS.add_left_cancel closed at Int's Group projection must type-check");

        let hand = k.const_(rp.int.add_left_cancel, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_left_cancel must exist");

        assert!(
            k.def_eq(generic_ty, hand_ty),
            "AlgS.add_left_cancel(AlgS.Group.ofAlg(Int.addGroup)) closed over \
             (a,b,c) must have the SAME TYPE as Int.add_left_cancel"
        );
    }
}
