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

// ---------------------------------------------------------------------------
// ADR-1592: `AlgS.OrderedRing` — `AlgS.CommRing`'s 23 fields restated (no
// inheritance, same "third copy" pattern the rest of this spine and `Alg.
// OrderedRing` both already use), plus `le`, a congruence field the setoid
// must carry by hand (`leCongr` -- `Eq` gets this step for free, `equiv`
// does not), and the same five order laws `Alg.OrderedRing` carries. Four
// of the five primitive-law field BUILDERS need no `equiv` at all (`le` is
// a plain relation and none of `le_refl`/`le_trans`/`add_le_add_left`/
// `mul_nonneg`'s STATEMENTS mention the carrier's equality), so they are
// reused verbatim from [`structures`] rather than duplicated; only
// `le_antisymm` (which must conclude `equiv`, not `Eq`) and `leCongr`
// (which has no `Eq`-flavored counterpart at all -- `Eq`'s own congruence
// is free) are new.
// ---------------------------------------------------------------------------

/// `forall a a' b b', equiv a a' -> equiv b b' -> le a b -> le a' b'` — the
/// congruence field a setoid must carry by hand for `le`, exactly as
/// `binop_congr_field_s` does for an operation.
fn le_congr_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    le_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let le = vals[le_idx];
            let va = k.fvar(V_A);
            let vap = k.fvar(V_AP);
            let vb = k.fvar(V_B);
            let vbp = k.fvar(V_BP);
            let haa = app2(k, equiv, va, vap);
            let hbb = app2(k, equiv, vb, vbp);
            let hle = app2(k, le, va, vb);
            let concl = app2(k, le, vap, vbp);
            let inner1 = arrow(k, hle, concl);
            let inner2 = arrow(k, hbb, inner1);
            let inner3 = arrow(k, haa, inner2);
            let t = pi_over(k, V_BP, a_ty, inner3);
            let t = pi_over(k, V_B, a_ty, t);
            let t = pi_over(k, V_AP, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b, le a b -> le b a -> equiv a b` — antisymmetry CONCLUDES
/// `equiv`, not `Eq` (the deliverable's explicit ask, and the shape
/// `CReal.equiv_of_le_le` already has verbatim).
fn le_antisymm_equiv_field_s(
    name: &'static str,
    carrier_idx: usize,
    equiv_idx: usize,
    le_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let equiv = vals[equiv_idx];
            let le = vals[le_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let hab = app2(k, le, va, vb);
            let hba = app2(k, le, vb, va);
            let concl = app2(k, equiv, va, vb);
            let inner = arrow(k, hba, concl);
            let inner2 = arrow(k, hab, inner);
            let t = pi_over(k, V_B, a_ty, inner2);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `AlgS.Ring`'s 22 fields, restated, plus `le`, `leCongr`, and five order
/// laws — 29 fields total. `rel_field`/`le_refl_field`/`le_trans_field`/
/// `add_le_add_left_field`/`mul_nonneg_field` are reused verbatim from
/// [`structures`] (their statements never mention `equiv`).
///
/// **Built over `AlgS.Ring` (22 fields), not `AlgS.CommRing` (23) --
/// necessary, not a simplification.** `Alg.OrderedRing` (ADR-1584) is
/// itself Ring-based (`Ring`'s 15 fields, no `mulComm`; none of the order
/// laws or `linarith::generic`'s fragment need commutativity), and
/// `AlgS.OrderedRing.ofAlg` (below) must select FROM an `Alg.OrderedRing`
/// value -- which carries no `mulComm` field to select in the first place.
/// A `CommRing`-based `AlgS.OrderedRing` would make that projection
/// ill-typed. `Int`/`Rat`/`CReal` are all commutative anyway, so nothing
/// downstream loses reach; only the record's own field list changes shape.
fn ordered_ring_fields_s() -> Vec<FieldSpec> {
    use idx::ring::{ADD, CARRIER, EQUIV, MUL, ZERO};
    let mut f = ring_fields_s(); // 0..21 (22 fields)
    f.push(structures::rel_field("le", CARRIER)); // 22
    let le_idx = f.len() - 1;
    f.push(le_congr_field_s("leCongr", CARRIER, EQUIV, le_idx)); // 23
    f.push(structures::le_refl_field("le_refl", CARRIER, le_idx)); // 24
    f.push(structures::le_trans_field("le_trans", CARRIER, le_idx)); // 25
    f.push(le_antisymm_equiv_field_s(
        "le_antisymm_equiv",
        CARRIER,
        EQUIV,
        le_idx,
    )); // 26
    f.push(structures::add_le_add_left_field(
        "add_le_add_left",
        CARRIER,
        ADD,
        le_idx,
    )); // 27
    f.push(structures::mul_nonneg_field(
        "mul_nonneg",
        CARRIER,
        MUL,
        ZERO,
        le_idx,
    )); // 28
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
    /// ADR-1592: `AlgS.OrderedRing` — `ring`'s 22 fields (NOT `comm_ring`'s
    /// 23: no `mulComm`, matching `Alg.OrderedRing`'s own Ring-based scope
    /// so `AlgS.OrderedRing.ofAlg` type-checks) plus `le`, `leCongr`, and
    /// five order laws.
    pub mod ordered_ring {
        pub use super::ring::*;
        pub const LE: usize = 22;
        pub const LE_CONGR: usize = 23;
        pub const LE_REFL: usize = 24;
        pub const LE_TRANS: usize = 25;
        pub const LE_ANTISYMM_EQUIV: usize = 26;
        pub const ADD_LE_ADD_LEFT: usize = 27;
        pub const MUL_NONNEG: usize = 28;
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
    /// ADR-1592.
    pub ordered_ring: NameId,
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
        ordered_ring: kernel.name_str(algs, "OrderedRing"),
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
    /// ADR-1592.
    pub ordered_ring: RecordNames,
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
    let ordered_ring = declare_record(
        kernel,
        logic,
        l0,
        l1,
        l2,
        p.ordered_ring,
        &ordered_ring_fields_s(),
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
        ordered_ring,
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

    /// `forall a a' b b', Eq a a' -> Eq b b' -> le a b -> le a' b'`,
    /// synthesized via two `subst` transports (`Eq.rec`-based, generalizing
    /// [`congr_arg`]'s shape to conclude a PROP membership rather than an
    /// operation-equality) -- the `ofAlg` counterpart of
    /// [`build_binop_congr`] for `AlgS.OrderedRing`'s new `leCongr` field,
    /// which has no `Eq`-flavored counterpart at all (`Eq`'s own congruence
    /// is free, so `Alg.OrderedRing` needs no such field).
    fn build_le_congr_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        lvl: LevelId,
        carrier: ExprId,
        le: ExprId,
    ) -> ExprId {
        const A: u64 = 21_150;
        const AP: u64 = 21_151;
        const B: u64 = 21_152;
        const BP: u64 = 21_153;
        const H1: u64 = 21_154;
        const H2: u64 = 21_155;
        const HLE: u64 = 21_156;
        const S1: u64 = 21_157;
        const S2: u64 = 21_158;
        let a = k.fvar(A);
        let ap = k.fvar(AP);
        let b = k.fvar(B);
        let bp = k.fvar(BP);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let hle = k.fvar(HLE);
        let hyp1_ty = crate::nat_prelude::structures::eq_of(k, lg, lvl, carrier, a, ap);
        let hyp2_ty = crate::nat_prelude::structures::eq_of(k, lg, lvl, carrier, b, bp);
        let hle_ty = app2(k, le, a, b);

        // step1 : le a' b, transport `hle` along h1 on (fun x => le x b).
        let step1 = crate::nat_prelude::structures::subst(
            k,
            lg,
            lvl,
            carrier,
            a,
            ap,
            h1,
            S1,
            &|k2, x| app2(k2, le, x, b),
            hle,
        );
        // step2 : le a' b', transport step1 along h2 on (fun y => le a' y).
        let step2 = crate::nat_prelude::structures::subst(
            k,
            lg,
            lvl,
            carrier,
            b,
            bp,
            h2,
            S2,
            &|k2, y| app2(k2, le, ap, y),
            step1,
        );

        let v = lam_over(k, HLE, hle_ty, step2);
        let v = lam_over(k, H2, hyp2_ty, v);
        let v = lam_over(k, H1, hyp1_ty, v);
        let v = lam_over(k, BP, carrier, v);
        let v = lam_over(k, B, carrier, v);
        let v = lam_over(k, AP, carrier, v);
        lam_over(k, A, carrier, v)
    }

    /// `AlgS.OrderedRing.ofAlg : Alg.OrderedRing -> AlgS.OrderedRing` --
    /// ADR-1592. Every LAW field (including `le_antisymm_equiv`, whose
    /// `Eq`-flavored source `le_antisymm` selector unfolds to EXACTLY
    /// `equiv a b` once `equiv := @Eq carrier`, the same load-bearing fact
    /// every other `ofAlg` projection in this module exploits) is the
    /// source record's own selector, unchanged; only the four
    /// equiv-infrastructure fields, the three inherited congruence fields
    /// (`addCongr`/`mulCongr`/`negCongr`), and `leCongr` (synthesized via
    /// [`build_le_congr_ofalg`] -- `le` has no `Eq`-flavored congruence
    /// field to reuse, since `Eq` gets it for free) need a fresh proof
    /// term.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn declare_ordered_ring_ofalg(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        alg_or: &RecordNames,
        algs_or: &RecordNames,
        algs_p: NameId,
    ) -> Result<NameId, KernelError> {
        use crate::nat_prelude::structures::idx::ordered_ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_LE_ADD_LEFT, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, LE,
            LE_ANTISYMM, LE_REFL, LE_TRANS, MUL, MUL_ASSOC, MUL_NONNEG, MUL_ONE_L, MUL_ONE_R, NEG,
            NEG_ADD, ONE, ZERO,
        };
        const R_FV: u64 = 21_290;
        let r = k.fvar(R_FV);
        let carrier = sel(k, alg_or, CARRIER, r);
        let zero = sel(k, alg_or, ZERO, r);
        let one = sel(k, alg_or, ONE, r);
        let add = sel(k, alg_or, ADD, r);
        let mul = sel(k, alg_or, MUL, r);
        let add_assoc = sel(k, alg_or, ADD_ASSOC, r);
        let add_comm = sel(k, alg_or, ADD_COMM, r);
        let add_zero = sel(k, alg_or, ADD_ZERO, r);
        let mul_assoc = sel(k, alg_or, MUL_ASSOC, r);
        let mul_one_l = sel(k, alg_or, MUL_ONE_L, r);
        let mul_one_r = sel(k, alg_or, MUL_ONE_R, r);
        let distrib_l = sel(k, alg_or, DISTRIB_L, r);
        let distrib_r = sel(k, alg_or, DISTRIB_R, r);
        let neg = sel(k, alg_or, NEG, r);
        let neg_add = sel(k, alg_or, NEG_ADD, r);
        let le = sel(k, alg_or, LE, r);
        let le_refl = sel(k, alg_or, LE_REFL, r);
        let le_trans = sel(k, alg_or, LE_TRANS, r);
        let le_antisymm_equiv = sel(k, alg_or, LE_ANTISYMM, r);
        let add_le_add_left = sel(k, alg_or, ADD_LE_ADD_LEFT, r);
        let mul_nonneg = sel(k, alg_or, MUL_NONNEG, r);

        let equiv = eq_partial(k, lg, l1, carrier);
        let equiv_refl = build_equiv_refl(k, lg, l1, carrier);
        let equiv_symm = build_equiv_symm(k, lg, l1, carrier);
        let equiv_trans = build_equiv_trans(k, lg, l1, carrier);
        let add_congr = build_binop_congr(k, lg, l1, carrier, add);
        let mul_congr = build_binop_congr(k, lg, l1, carrier, mul);
        let neg_congr = build_unop_congr(k, lg, l1, carrier, neg);
        let le_congr = build_le_congr_ofalg(k, lg, l1, carrier, le);

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
            le,
            le_congr,
            le_refl,
            le_trans,
            le_antisymm_equiv,
            add_le_add_left,
            mul_nonneg,
        ];
        declare_projection(k, algs_p, alg_or, algs_or, &args, R_FV)
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
// `AlgS.Group`-level generic theorems (ADR-1592, closing the gap ADR-1590 §3
// named: "AlgS has no Group-level generic theorem at all" to derive
// `Alg.neg_neg` from). Mirrors `rat_prelude::algebra_instances::
// build_group_inv_unique`/`rat_prelude::algebra_ext::build_neg_neg` (the
// `Eq`-flavored spine's own Group-level pair) exactly, `Eq.trans`/`symm_of`/
// `congr_arg` replaced by the record's own `equivTrans`/`equivSymm`/
// `opCongr`, the same substitution `declare_add_left_cancel` above already
// made for `Alg.mul_left_cancel`.
// ---------------------------------------------------------------------------

/// `AlgS.inv_unique : forall (G:Group)(a b c:G.carrier), G.equiv (G.op b a)
/// G.e -> G.equiv (G.op a c) G.e -> G.equiv b c`. `b = b*e = b*(a*c) =
/// (b*a)*c = e*c = c`, the exact shape `Alg.groupInvUnique` uses.
#[allow(clippy::similar_names, clippy::too_many_lines)]
fn build_group_inv_unique_s(k: &mut Kernel, group: &RecordNames) -> (ExprId, ExprId) {
    use idx::group::{
        ASSOC, CARRIER, E, EQUIV, EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, IDENT_L, IDENT_R, OP,
        OP_CONGR,
    };
    const G_FV: u64 = 21_520;
    const A_FV: u64 = 21_521;
    const B_FV: u64 = 21_522;
    const C_FV: u64 = 21_523;
    const H1_FV: u64 = 21_524;
    const H2_FV: u64 = 21_525;

    let group_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(G_FV);
    let carrier = sel(k, group, CARRIER, g);
    let equiv = sel(k, group, EQUIV, g);
    let equiv_refl = sel(k, group, EQUIV_REFL, g);
    let equiv_symm = sel(k, group, EQUIV_SYMM, g);
    let equiv_trans = sel(k, group, EQUIV_TRANS, g);
    let op = sel(k, group, OP, g);
    let op_congr = sel(k, group, OP_CONGR, g);
    let e = sel(k, group, E, g);
    let ident_l = sel(k, group, IDENT_L, g);
    let ident_r = sel(k, group, IDENT_R, g);
    let assoc = sel(k, group, ASSOC, g);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);

    let op_b_a = t_app(k, op, &[b, a]);
    let op_a_c = t_app(k, op, &[a, c]);
    let h1_ty = app2(k, equiv, op_b_a, e); // equiv (op b a) e
    let h2_ty = app2(k, equiv, op_a_c, e); // equiv (op a c) e
    let h1 = k.fvar(H1_FV);
    let h2 = k.fvar(H2_FV);

    // Step A: identR(b) : equiv (op b e) b ; symm -> equiv b (op b e)
    let op_b_e = t_app(k, op, &[b, e]);
    let h_a = k.app(ident_r, b);
    let symm_ha = t_app(k, equiv_symm, &[op_b_e, b, h_a]);

    // Step B: symm(h2) : equiv e (op a c) ; opCongr (op b .) -> equiv (op b e)
    // (op b (op a c))
    let symm_h2 = t_app(k, equiv_symm, &[op_a_c, e, h2]);
    let op_b_opac = t_app(k, op, &[b, op_a_c]);
    let refl_b = t_app(k, equiv_refl, &[b]);
    let step_b = t_app(k, op_congr, &[b, b, e, op_a_c, refl_b, symm_h2]);

    let r1 = t_app(k, equiv_trans, &[b, op_b_e, op_b_opac, symm_ha, step_b]);

    // Step C: assoc(b,a,c) : equiv (op (op b a) c) (op b (op a c)) ; symm.
    let op_ba_c = t_app(k, op, &[op_b_a, c]);
    let assoc_bac = t_app(k, assoc, &[b, a, c]);
    let step_c = t_app(k, equiv_symm, &[op_ba_c, op_b_opac, assoc_bac]);

    let r2 = t_app(k, equiv_trans, &[b, op_b_opac, op_ba_c, r1, step_c]);

    // Step D: opCongr (. c) on h1 : equiv (op b a) e => equiv (op (op b a) c)
    // (op e c)
    let op_e_c = t_app(k, op, &[e, c]);
    let refl_c = t_app(k, equiv_refl, &[c]);
    let step_d = t_app(k, op_congr, &[op_b_a, e, c, c, h1, refl_c]);

    let r3 = t_app(k, equiv_trans, &[b, op_ba_c, op_e_c, r2, step_d]);

    // Step E: identL(c) : equiv (op e c) c.
    let step_e = k.app(ident_l, c);

    let r4 = t_app(k, equiv_trans, &[b, op_e_c, c, r3, step_e]);

    let value = lam_over(k, H2_FV, h2_ty, r4);
    let value = lam_over(k, H1_FV, h1_ty, value);
    let value = lam_over(k, C_FV, carrier, value);
    let value = lam_over(k, B_FV, carrier, value);
    let value = lam_over(k, A_FV, carrier, value);
    let value = lam_over(k, G_FV, group_ty, value);

    let concl = app2(k, equiv, b, c);
    let ty = pi_over(k, H2_FV, h2_ty, concl);
    let ty = pi_over(k, H1_FV, h1_ty, ty);
    let ty = pi_over(k, C_FV, carrier, ty);
    let ty = pi_over(k, B_FV, carrier, ty);
    let ty = pi_over(k, A_FV, carrier, ty);
    let ty = pi_over(k, G_FV, group_ty, ty);

    (ty, value)
}

pub(crate) fn declare_inv_unique(
    k: &mut Kernel,
    group: &RecordNames,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    let (ty, value) = build_group_inv_unique_s(k, group);
    let name = k.name_str(algs_p, "inv_unique");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.invInv : forall (G:Group)(a:G.carrier), G.equiv (G.inv (G.inv a))
/// a`. A direct instantiation of `AlgS.inv_unique` at `(a := G.inv a, b :=
/// G.inv(G.inv a), c := a)`, `h1 := invL(G.inv a)`, `h2 := invL a` -- no new
/// proof engineering, mirroring `Alg.neg_neg`'s own proof
/// (`rat_prelude::algebra_ext::build_neg_neg`) exactly.
///
/// **Named `invInv`, not `neg_neg`.** `AlgS.neg_neg` (ADR-1588) already
/// names a DIFFERENT, `Ring`-scoped theorem (`equiv (R.neg (R.neg a)) a`,
/// built from `negAdd`/`addComm`/`addAssoc` over `AlgS.Ring`'s additive
/// structure); this one is stated over `AlgS.Group`'s generic `inv`, the
/// scope `Alg.neg_neg` actually has. Reusing the name would collide with an
/// existing, differently-typed, fact-ledger-pinned declaration
/// (`F-algs-neg-neg.json`) -- see ADR-1592.
pub(crate) fn declare_inv_inv(
    k: &mut Kernel,
    group: &RecordNames,
    inv_unique_name: NameId,
    algs_p: NameId,
) -> Result<NameId, KernelError> {
    use idx::group::{CARRIER, EQUIV, INV, INV_L};
    const G_FV: u64 = 21_530;
    const A_FV: u64 = 21_531;

    let group_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(G_FV);
    let carrier = sel(k, group, CARRIER, g);
    let equiv = sel(k, group, EQUIV, g);
    let inv = sel(k, group, INV, g);
    let inv_l = sel(k, group, INV_L, g);
    let a = k.fvar(A_FV);
    let inv_a = k.app(inv, a);
    let inv_inv_a = k.app(inv, inv_a);

    let thm = k.const_(inv_unique_name, vec![]);
    let h1 = k.app(inv_l, inv_a); // equiv (op (inv (inv a)) (inv a)) e
    let h2 = k.app(inv_l, a); // equiv (op (inv a) a) e
    let applied = {
        let e1 = k.app(thm, g);
        let e2 = k.app(e1, inv_a);
        let e3 = k.app(e2, inv_inv_a);
        let e4 = k.app(e3, a);
        let e5 = k.app(e4, h1);
        k.app(e5, h2)
    };

    let value = lam_over(k, A_FV, carrier, applied);
    let value = lam_over(k, G_FV, group_ty, value);

    let concl = app2(k, equiv, inv_inv_a, a);
    let ty = pi_over(k, A_FV, carrier, concl);
    let ty = pi_over(k, G_FV, group_ty, ty);

    let name = k.name_str(algs_p, "invInv");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// `AlgS.CommRing.toCommGroupS` -- the additive-group forgetful projection
// ADR-1590's own `ring_s_additive_group_value` term-builder left as an
// un-named, `#[cfg(test)]`-gated helper ("out of scope here", ADR-1590's
// Alternatives). This is that same construction, promoted to a real
// declared name and widened to `CommGroup` (adding the `comm` field --
// `addComm`, already available) rather than `Group`, matching the
// deliverable's literal ask. `identL`/`invL` are still DERIVED from
// `addComm`+`addZero`/`negAdd`, unchanged in substance.
// ---------------------------------------------------------------------------

pub(crate) fn declare_comm_ring_to_comm_group_s(
    k: &mut Kernel,
    st: &StructuresSRecordNames,
    p: &StructuresSNames,
) -> Result<NameId, KernelError> {
    use idx::ring as ridx;
    const R_FV: u64 = 21_430;
    const A_FV: u64 = 21_431;
    const B_FV: u64 = 21_432;

    let comm_ring = &st.comm_ring;
    let r = k.fvar(R_FV);
    let carrier = sel(k, comm_ring, ridx::CARRIER, r);
    let equiv = sel(k, comm_ring, ridx::EQUIV, r);
    let equiv_refl = sel(k, comm_ring, ridx::EQUIV_REFL, r);
    let equiv_symm = sel(k, comm_ring, ridx::EQUIV_SYMM, r);
    let equiv_trans = sel(k, comm_ring, ridx::EQUIV_TRANS, r);
    let add = sel(k, comm_ring, ridx::ADD, r);
    let add_congr = sel(k, comm_ring, ridx::ADD_CONGR, r);
    let zero = sel(k, comm_ring, ridx::ZERO, r);
    let neg = sel(k, comm_ring, ridx::NEG, r);
    let neg_congr = sel(k, comm_ring, ridx::NEG_CONGR, r);
    let add_assoc = sel(k, comm_ring, ridx::ADD_ASSOC, r);
    let add_comm = sel(k, comm_ring, ridx::ADD_COMM, r);
    let add_zero = sel(k, comm_ring, ridx::ADD_ZERO, r); // identR
    let neg_add = sel(k, comm_ring, ridx::NEG_ADD, r); // invR

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
    let nb_add = k.app(neg_add, b);
    let inv_l_body = t_app(k, equiv_trans, &[add_nbb, add_bnb, zero, comm_nb_b, nb_add]);
    let inv_l = lam_over(k, B_FV, carrier, inv_l_body);

    let value = structures::mk_instance(
        k,
        &st.comm_group,
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
            add_comm,
        ],
    );
    let comm_ring_ty0 = k.const_(comm_ring.ind, vec![]);
    let value = lam_over(k, R_FV, comm_ring_ty0, value);

    let ty = {
        let dom = k.const_(comm_ring.ind, vec![]);
        let cod = k.const_(st.comm_group.ind, vec![]);
        arrow(k, dom, cod)
    };

    let name = k.name_str(p.comm_ring, "toCommGroupS");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.CommGroup.toGroupS : AlgS.CommGroup -> AlgS.Group` -- the same
/// PREFIX-projection shape `AlgS.CommRing.toRingS` and `Alg.CommGroup.
/// toGroup` both already use (`CommGroup`'s first 15 fields ARE `Group`'s
/// field list verbatim), needed to reach a plain `Group` value (for
/// `AlgS.add_left_cancel`/`AlgS.inv_unique`/`AlgS.invInv`, all stated over
/// `Group`, not `CommGroup`) from `AlgS.CommRing.toCommGroupS`'s output.
pub(crate) fn declare_comm_group_to_group_s(
    k: &mut Kernel,
    st: &StructuresSRecordNames,
    p: &StructuresSNames,
) -> Result<NameId, KernelError> {
    use idx::group::INV_R;
    const G_FV: u64 = 21_440;
    let g = k.fvar(G_FV);
    let mut args = Vec::with_capacity(INV_R + 1);
    for i in 0..=INV_R {
        args.push(sel(k, &st.comm_group, i, g));
    }
    let value = structures::mk_instance(k, &st.group, &args);
    let comm_group_ty0 = k.const_(st.comm_group.ind, vec![]);
    let value = lam_over(k, G_FV, comm_group_ty0, value);
    let ty = {
        let dom = k.const_(st.comm_group.ind, vec![]);
        let cod = k.const_(st.group.ind, vec![]);
        arrow(k, dom, cod)
    };
    let name = k.name_str(p.comm_group, "toGroupS");
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
// ADR-1595 / roadmap W2-8: the FIRST ISOMORPHISM THEOREM over `AlgS.Group`,
// built by the SETOID route -- no `Quot`, no `Quot.sound`, no `funext`.
//
// The construction this section exists to MEASURE (see ADR-1595): a quotient
// group is presented not as a new carrier of equivalence classes but as the
// SAME carrier under a COARSER equivalence. `AlgS.Hom.quotient` is a genuine
// `AlgS.Group` value whose `carrier` is `G.carrier` and whose `equiv` is
// `fun a b => H.equiv (f a) (f b)` -- the kernel congruence. Everything a
// real `Quot` would give for free (that the relation is an equivalence, that
// the operations descend, that the induced map is well defined) has to be
// supplied here as an explicit field, and the count of those fields is the
// deliverable.
// ---------------------------------------------------------------------------

const FI_G_FV: u64 = 21_700;
const FI_H_FV: u64 = 21_701;
const FI_F_FV: u64 = 21_702;
const FI_FC_FV: u64 = 21_703;
const FI_FM_FV: u64 = 21_704;
const FI_A_FV: u64 = 21_705;
const FI_B_FV: u64 = 21_706;
const FI_C_FV: u64 = 21_707;
const FI_AP_FV: u64 = 21_708;
const FI_BP_FV: u64 = 21_709;
const FI_H1_FV: u64 = 21_710;
const FI_H2_FV: u64 = 21_711;
const FI_Y_FV: u64 = 21_712;

/// Every selector of the two groups plus the homomorphism data, resolved
/// once against the five outer free variables `G H f fCongr fMul`.
struct HomCtx {
    group_ty: ExprId,
    g: ExprId,
    h: ExprId,
    f: ExprId,
    fc: ExprId,
    fm: ExprId,
    f_ty: ExprId,
    fc_ty: ExprId,
    fm_ty: ExprId,
    gc: ExprId,
    g_op: ExprId,
    g_e: ExprId,
    g_inv: ExprId,
    g_assoc: ExprId,
    g_ident_l: ExprId,
    g_ident_r: ExprId,
    g_inv_l: ExprId,
    g_inv_r: ExprId,
    hc: ExprId,
    h_equiv: ExprId,
    h_refl: ExprId,
    h_symm: ExprId,
    h_trans: ExprId,
    h_op: ExprId,
    h_op_congr: ExprId,
    h_e: ExprId,
    h_inv: ExprId,
    h_inv_congr: ExprId,
    h_ident_r: ExprId,
    h_inv_l: ExprId,
    h_inv_r: ExprId,
}

fn hom_ctx(k: &mut Kernel, group: &RecordNames) -> HomCtx {
    use idx::group::{
        ASSOC, CARRIER, E, EQUIV, EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, IDENT_L, IDENT_R, INV,
        INV_CONGR, INV_L, INV_R, OP, OP_CONGR,
    };
    let group_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(FI_G_FV);
    let h = k.fvar(FI_H_FV);
    let f = k.fvar(FI_F_FV);
    let fc = k.fvar(FI_FC_FV);
    let fm = k.fvar(FI_FM_FV);

    let gc = sel(k, group, CARRIER, g);
    let g_equiv = sel(k, group, EQUIV, g);
    let g_op = sel(k, group, OP, g);
    let g_e = sel(k, group, E, g);
    let g_inv = sel(k, group, INV, g);
    let g_assoc = sel(k, group, ASSOC, g);
    let g_ident_l = sel(k, group, IDENT_L, g);
    let g_ident_r = sel(k, group, IDENT_R, g);
    let g_inv_l = sel(k, group, INV_L, g);
    let g_inv_r = sel(k, group, INV_R, g);

    let hc = sel(k, group, CARRIER, h);
    let h_equiv = sel(k, group, EQUIV, h);
    let h_refl = sel(k, group, EQUIV_REFL, h);
    let h_symm = sel(k, group, EQUIV_SYMM, h);
    let h_trans = sel(k, group, EQUIV_TRANS, h);
    let h_op = sel(k, group, OP, h);
    let h_op_congr = sel(k, group, OP_CONGR, h);
    let h_e = sel(k, group, E, h);
    let h_inv = sel(k, group, INV, h);
    let h_inv_congr = sel(k, group, INV_CONGR, h);
    let h_ident_r = sel(k, group, IDENT_R, h);
    let h_inv_l = sel(k, group, INV_L, h);
    let h_inv_r = sel(k, group, INV_R, h);

    // f : G.carrier -> H.carrier
    let f_ty = arrow(k, gc, hc);

    // fCongr : forall (a b : G.carrier), G.equiv a b -> H.equiv (f a) (f b)
    let fc_ty = {
        let a = k.fvar(FI_A_FV);
        let b = k.fvar(FI_B_FV);
        let hyp = app2(k, g_equiv, a, b);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let concl = app2(k, h_equiv, fa, fb);
        let t = arrow(k, hyp, concl);
        let t = pi_over(k, FI_B_FV, gc, t);
        pi_over(k, FI_A_FV, gc, t)
    };

    // fMul : forall (a b : G.carrier),
    //          H.equiv (f (G.op a b)) (H.op (f a) (f b))
    let fm_ty = {
        let a = k.fvar(FI_A_FV);
        let b = k.fvar(FI_B_FV);
        let ab = t_app(k, g_op, &[a, b]);
        let f_ab = k.app(f, ab);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let rhs = t_app(k, h_op, &[fa, fb]);
        let concl = app2(k, h_equiv, f_ab, rhs);
        let t = pi_over(k, FI_B_FV, gc, concl);
        pi_over(k, FI_A_FV, gc, t)
    };

    HomCtx {
        group_ty,
        g,
        h,
        f,
        fc,
        fm,
        f_ty,
        fc_ty,
        fm_ty,
        gc,
        g_op,
        g_e,
        g_inv,
        g_assoc,
        g_ident_l,
        g_ident_r,
        g_inv_l,
        g_inv_r,
        hc,
        h_equiv,
        h_refl,
        h_symm,
        h_trans,
        h_op,
        h_op_congr,
        h_e,
        h_inv,
        h_inv_congr,
        h_ident_r,
        h_inv_l,
        h_inv_r,
    }
}

/// Close a statement over `G H f` (the three binders every `AlgS.Hom`
/// DEFINITION needs).
fn close_ghf(k: &mut Kernel, c: &HomCtx, body: ExprId, lam: bool) -> ExprId {
    let t = if lam {
        lam_over(k, FI_F_FV, c.f_ty, body)
    } else {
        pi_over(k, FI_F_FV, c.f_ty, body)
    };
    let t = if lam {
        lam_over(k, FI_H_FV, c.group_ty, t)
    } else {
        pi_over(k, FI_H_FV, c.group_ty, t)
    };
    if lam {
        lam_over(k, FI_G_FV, c.group_ty, t)
    } else {
        pi_over(k, FI_G_FV, c.group_ty, t)
    }
}

/// Close a statement over `G H f fCongr fMul` (the five binders every
/// `AlgS.Hom` THEOREM needs).
fn close_hom(k: &mut Kernel, c: &HomCtx, body: ExprId, lam: bool) -> ExprId {
    let t = if lam {
        lam_over(k, FI_FM_FV, c.fm_ty, body)
    } else {
        pi_over(k, FI_FM_FV, c.fm_ty, body)
    };
    let t = if lam {
        lam_over(k, FI_FC_FV, c.fc_ty, t)
    } else {
        pi_over(k, FI_FC_FV, c.fc_ty, t)
    };
    close_ghf(k, c, t, lam)
}

// -- tiny term shorthands over the codomain group `H` -----------------------

fn heq(k: &mut Kernel, c: &HomCtx, x: ExprId, y: ExprId) -> ExprId {
    app2(k, c.h_equiv, x, y)
}

fn hsymm(k: &mut Kernel, c: &HomCtx, x: ExprId, y: ExprId, p: ExprId) -> ExprId {
    t_app(k, c.h_symm, &[x, y, p])
}

fn htrans(
    k: &mut Kernel,
    c: &HomCtx,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    p: ExprId,
    q: ExprId,
) -> ExprId {
    t_app(k, c.h_trans, &[x, y, z, p, q])
}

/// `AlgS.Hom.ker : forall (G H : Group) (f : G.carrier -> H.carrier),
/// G.carrier -> Prop := fun G H f a => H.equiv (f a) H.e`. The kernel of a
/// homomorphism as a PREDICATE -- a subgroup is a predicate here, not a
/// carrier, because this kernel has no subtypes.
pub(crate) fn declare_hom_ker(
    k: &mut Kernel,
    group: &RecordNames,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let a = k.fvar(FI_A_FV);
    let fa = k.app(c.f, a);
    let body = heq(k, &c, fa, c.h_e);
    let value = lam_over(k, FI_A_FV, c.gc, body);
    let value = close_ghf(k, &c, value, true);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = arrow(k, c.gc, prop);
    let ty = close_ghf(k, &c, ty, false);

    let name = k.name_str(hom_ns, "ker");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Hom.kerEquiv : forall G H f, G.carrier -> G.carrier -> Prop :=
/// fun G H f a b => H.equiv (f a) (f b)`. THE induced equivalence -- what
/// `Quot` would build a new type out of, and what the setoid route instead
/// keeps as a relation on the ORIGINAL carrier.
pub(crate) fn declare_hom_ker_equiv(
    k: &mut Kernel,
    group: &RecordNames,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let a = k.fvar(FI_A_FV);
    let b = k.fvar(FI_B_FV);
    let fa = k.app(c.f, a);
    let fb = k.app(c.f, b);
    let body = heq(k, &c, fa, fb);
    let value = lam_over(k, FI_B_FV, c.gc, body);
    let value = lam_over(k, FI_A_FV, c.gc, value);
    let value = close_ghf(k, &c, value, true);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = arrow(k, c.gc, prop);
    let ty = arrow(k, c.gc, ty);
    let ty = close_ghf(k, &c, ty, false);

    let name = k.name_str(hom_ns, "kerEquiv");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Hom.image : forall G H f, H.carrier -> Prop := fun G H f y =>
/// Exists G.carrier (fun a => H.equiv (f a) y)`. The image, again as a
/// predicate on `H.carrier` rather than a carrier of its own.
pub(crate) fn declare_hom_image(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let y = k.fvar(FI_Y_FV);
    let a = k.fvar(FI_A_FV);
    let fa = k.app(c.f, a);
    let inner = heq(k, &c, fa, y);
    let pred = lam_over(k, FI_A_FV, c.gc, inner);
    let ex = k.const_(lg.exists_, vec![l1]);
    let body = t_app(k, ex, &[c.gc, pred]);
    let value = lam_over(k, FI_Y_FV, c.hc, body);
    let value = close_ghf(k, &c, value, true);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = arrow(k, c.hc, prop);
    let ty = close_ghf(k, &c, ty, false);

    let name = k.name_str(hom_ns, "image");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Hom.mapOne : forall G H f fCongr fMul, H.equiv (f G.e) H.e`.
/// `f e * f e ~ f (e * e) ~ f e ~ f e * e`, then cancel on the left.
pub(crate) fn declare_hom_map_one(
    k: &mut Kernel,
    group: &RecordNames,
    add_left_cancel: NameId,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let x = k.app(c.f, c.g_e); // x := f G.e
    let ee = t_app(k, c.g_op, &[c.g_e, c.g_e]);
    let f_ee = k.app(c.f, ee);
    let xx = t_app(k, c.h_op, &[x, x]);
    let x_he = t_app(k, c.h_op, &[x, c.h_e]);

    // s1 : H.equiv (f (e*e)) (x*x)
    let s1 = t_app(k, c.fm, &[c.g_e, c.g_e]);
    // s3 : H.equiv (f (e*e)) x, from G.identL e : G.equiv (e*e) e
    let ident_l_e = k.app(c.g_ident_l, c.g_e);
    let s3 = t_app(k, c.fc, &[ee, c.g_e, ident_l_e]);
    // s5 : H.equiv (x*x) x
    let s4 = hsymm(k, &c, f_ee, xx, s1);
    let s5 = htrans(k, &c, xx, f_ee, x, s4, s3);
    // s7 : H.equiv x (x*e)
    let s6 = k.app(c.h_ident_r, x);
    let s7 = hsymm(k, &c, x_he, x, s6);
    // s8 : H.equiv (x*x) (x*e)
    let s8 = htrans(k, &c, xx, x, x_he, s5, s7);

    let cancel = k.const_(add_left_cancel, vec![]);
    let body = t_app(k, cancel, &[c.h, x, x, c.h_e, s8]);
    let value = close_hom(k, &c, body, true);

    let concl = heq(k, &c, x, c.h_e);
    let ty = close_hom(k, &c, concl, false);

    let name = k.name_str(hom_ns, "mapOne");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Hom.mapInv : forall G H f fCongr fMul (a : G.carrier),
/// H.equiv (f (G.inv a)) (H.inv (f a))` -- `AlgS.inv_unique` at
/// `(f a, f (inv a), H.inv (f a))`.
pub(crate) fn declare_hom_map_inv(
    k: &mut Kernel,
    group: &RecordNames,
    inv_unique: NameId,
    map_one: NameId,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let a = k.fvar(FI_A_FV);
    let inv_a = k.app(c.g_inv, a);
    let f_inv_a = k.app(c.f, inv_a);
    let fa = k.app(c.f, a);
    let h_inv_fa = k.app(c.h_inv, fa);
    let f_e = k.app(c.f, c.g_e);

    // t1 : H.equiv (f (inv a * a)) ((f (inv a)) * (f a))
    let ia_a = t_app(k, c.g_op, &[inv_a, a]);
    let f_ia_a = k.app(c.f, ia_a);
    let prod = t_app(k, c.h_op, &[f_inv_a, fa]);
    let t1 = t_app(k, c.fm, &[inv_a, a]);
    let t2 = hsymm(k, &c, f_ia_a, prod, t1);
    // t4 : H.equiv (f (inv a * a)) (f e)
    let inv_l_a = k.app(c.g_inv_l, a);
    let t4 = t_app(k, c.fc, &[ia_a, c.g_e, inv_l_a]);
    // t5 : H.equiv (f e) H.e
    let mo = k.const_(map_one, vec![]);
    let t5 = t_app(k, mo, &[c.g, c.h, c.f, c.fc, c.fm]);
    let t6 = htrans(k, &c, f_ia_a, f_e, c.h_e, t4, t5);
    // h1 : H.equiv ((f (inv a)) * (f a)) H.e
    let h1 = htrans(k, &c, prod, f_ia_a, c.h_e, t2, t6);
    // h2 : H.equiv ((f a) * (H.inv (f a))) H.e
    let h2 = k.app(c.h_inv_r, fa);

    let iu = k.const_(inv_unique, vec![]);
    let body = t_app(k, iu, &[c.h, fa, f_inv_a, h_inv_fa, h1, h2]);
    let value = lam_over(k, FI_A_FV, c.gc, body);
    let value = close_hom(k, &c, value, true);

    let concl = heq(k, &c, f_inv_a, h_inv_fa);
    let ty = pi_over(k, FI_A_FV, c.gc, concl);
    let ty = close_hom(k, &c, ty, false);

    let name = k.name_str(hom_ns, "mapInv");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// **Congruence obligation 1 of 2** (the ones a real `Quot` discharges for
/// free): `AlgS.Hom.kerEquivOpCongr : forall G H f fCongr fMul a a' b b',
/// H.equiv (f a) (f a') -> H.equiv (f b) (f b') ->
/// H.equiv (f (G.op a b)) (f (G.op a' b'))`. This is `AlgS.Group`'s
/// `opCongr` field for the quotient, and nothing but this proof supplies it.
pub(crate) fn declare_ker_equiv_op_congr(
    k: &mut Kernel,
    group: &RecordNames,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let a = k.fvar(FI_A_FV);
    let ap = k.fvar(FI_AP_FV);
    let b = k.fvar(FI_B_FV);
    let bp = k.fvar(FI_BP_FV);
    let fa = k.app(c.f, a);
    let fap = k.app(c.f, ap);
    let fb = k.app(c.f, b);
    let fbp = k.app(c.f, bp);
    let hyp1_ty = heq(k, &c, fa, fap);
    let hyp2_ty = heq(k, &c, fb, fbp);
    let h1 = k.fvar(FI_H1_FV);
    let h2 = k.fvar(FI_H2_FV);

    let ab = t_app(k, c.g_op, &[a, b]);
    let apbp = t_app(k, c.g_op, &[ap, bp]);
    let f_ab = k.app(c.f, ab);
    let f_apbp = k.app(c.f, apbp);
    let prod = t_app(k, c.h_op, &[fa, fb]);
    let prod_p = t_app(k, c.h_op, &[fap, fbp]);

    let u1 = t_app(k, c.fm, &[a, b]);
    let u2 = t_app(k, c.h_op_congr, &[fa, fap, fb, fbp, h1, h2]);
    let u3 = htrans(k, &c, f_ab, prod, prod_p, u1, u2);
    let u4 = t_app(k, c.fm, &[ap, bp]);
    let u5 = hsymm(k, &c, f_apbp, prod_p, u4);
    let body = htrans(k, &c, f_ab, prod_p, f_apbp, u3, u5);

    let value = lam_over(k, FI_H2_FV, hyp2_ty, body);
    let value = lam_over(k, FI_H1_FV, hyp1_ty, value);
    let value = lam_over(k, FI_BP_FV, c.gc, value);
    let value = lam_over(k, FI_B_FV, c.gc, value);
    let value = lam_over(k, FI_AP_FV, c.gc, value);
    let value = lam_over(k, FI_A_FV, c.gc, value);
    let value = close_hom(k, &c, value, true);

    let concl = heq(k, &c, f_ab, f_apbp);
    let ty = pi_over(k, FI_H2_FV, hyp2_ty, concl);
    let ty = pi_over(k, FI_H1_FV, hyp1_ty, ty);
    let ty = pi_over(k, FI_BP_FV, c.gc, ty);
    let ty = pi_over(k, FI_B_FV, c.gc, ty);
    let ty = pi_over(k, FI_AP_FV, c.gc, ty);
    let ty = pi_over(k, FI_A_FV, c.gc, ty);
    let ty = close_hom(k, &c, ty, false);

    let name = k.name_str(hom_ns, "kerEquivOpCongr");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// **Congruence obligation 2 of 2**: `AlgS.Hom.kerEquivInvCongr`, the
/// quotient's `invCongr` field.
pub(crate) fn declare_ker_equiv_inv_congr(
    k: &mut Kernel,
    group: &RecordNames,
    map_inv: NameId,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let a = k.fvar(FI_A_FV);
    let ap = k.fvar(FI_AP_FV);
    let fa = k.app(c.f, a);
    let fap = k.app(c.f, ap);
    let hyp_ty = heq(k, &c, fa, fap);
    let h1 = k.fvar(FI_H1_FV);

    let inv_a = k.app(c.g_inv, a);
    let inv_ap = k.app(c.g_inv, ap);
    let f_inv_a = k.app(c.f, inv_a);
    let f_inv_ap = k.app(c.f, inv_ap);
    let hi_fa = k.app(c.h_inv, fa);
    let hi_fap = k.app(c.h_inv, fap);

    let mi = k.const_(map_inv, vec![]);
    let mi_app = t_app(k, mi, &[c.g, c.h, c.f, c.fc, c.fm]);
    let v1 = k.app(mi_app, a);
    let v2 = t_app(k, c.h_inv_congr, &[fa, fap, h1]);
    let v3 = htrans(k, &c, f_inv_a, hi_fa, hi_fap, v1, v2);
    let v4 = k.app(mi_app, ap);
    let v5 = hsymm(k, &c, f_inv_ap, hi_fap, v4);
    let body = htrans(k, &c, f_inv_a, hi_fap, f_inv_ap, v3, v5);

    let value = lam_over(k, FI_H1_FV, hyp_ty, body);
    let value = lam_over(k, FI_AP_FV, c.gc, value);
    let value = lam_over(k, FI_A_FV, c.gc, value);
    let value = close_hom(k, &c, value, true);

    let concl = heq(k, &c, f_inv_a, f_inv_ap);
    let ty = pi_over(k, FI_H1_FV, hyp_ty, concl);
    let ty = pi_over(k, FI_AP_FV, c.gc, ty);
    let ty = pi_over(k, FI_A_FV, c.gc, ty);
    let ty = close_hom(k, &c, ty, false);

    let name = k.name_str(hom_ns, "kerEquivInvCongr");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Hom.quotient : forall G H f fCongr fMul, AlgS.Group` -- **the
/// quotient group `G / ker f`, with no `Quot` anywhere**. Carrier is
/// `G.carrier` UNCHANGED; the quotient happens entirely in the `equiv`
/// field. All fifteen `AlgS.Group` fields are listed in the body so the
/// per-field cost of the setoid route is readable off the source.
pub(crate) fn declare_hom_quotient(
    k: &mut Kernel,
    group: &RecordNames,
    op_congr_thm: NameId,
    inv_congr_thm: NameId,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);

    // 1 equiv := fun a b => H.equiv (f a) (f b)
    let equiv_val = {
        let a = k.fvar(FI_A_FV);
        let b = k.fvar(FI_B_FV);
        let fa = k.app(c.f, a);
        let fb = k.app(c.f, b);
        let body = heq(k, &c, fa, fb);
        let t = lam_over(k, FI_B_FV, c.gc, body);
        lam_over(k, FI_A_FV, c.gc, t)
    };
    // 2 equivRefl := fun a => H.equivRefl (f a)
    let refl_val = {
        let a = k.fvar(FI_A_FV);
        let fa = k.app(c.f, a);
        let body = k.app(c.h_refl, fa);
        lam_over(k, FI_A_FV, c.gc, body)
    };
    // 3 equivSymm := fun a b h => H.equivSymm (f a) (f b) h
    let symm_val = {
        let a = k.fvar(FI_A_FV);
        let b = k.fvar(FI_B_FV);
        let fa = k.app(c.f, a);
        let fb = k.app(c.f, b);
        let hyp = heq(k, &c, fa, fb);
        let hv = k.fvar(FI_H1_FV);
        let body = hsymm(k, &c, fa, fb, hv);
        let t = lam_over(k, FI_H1_FV, hyp, body);
        let t = lam_over(k, FI_B_FV, c.gc, t);
        lam_over(k, FI_A_FV, c.gc, t)
    };
    // 4 equivTrans := fun a b c h1 h2 => H.equivTrans (f a) (f b) (f c) h1 h2
    let trans_val = {
        let a = k.fvar(FI_A_FV);
        let b = k.fvar(FI_B_FV);
        let cv = k.fvar(FI_C_FV);
        let fa = k.app(c.f, a);
        let fb = k.app(c.f, b);
        let fcv = k.app(c.f, cv);
        let hyp1 = heq(k, &c, fa, fb);
        let hyp2 = heq(k, &c, fb, fcv);
        let h1 = k.fvar(FI_H1_FV);
        let h2 = k.fvar(FI_H2_FV);
        let body = htrans(k, &c, fa, fb, fcv, h1, h2);
        let t = lam_over(k, FI_H2_FV, hyp2, body);
        let t = lam_over(k, FI_H1_FV, hyp1, t);
        let t = lam_over(k, FI_C_FV, c.gc, t);
        let t = lam_over(k, FI_B_FV, c.gc, t);
        lam_over(k, FI_A_FV, c.gc, t)
    };
    // 6 opCongr, 9 invCongr: the two hand-discharged congruence obligations.
    let five = [c.g, c.h, c.f, c.fc, c.fm];
    let op_congr_val = {
        let t = k.const_(op_congr_thm, vec![]);
        t_app(k, t, &five)
    };
    let inv_congr_val = {
        let t = k.const_(inv_congr_thm, vec![]);
        t_app(k, t, &five)
    };

    let a = k.fvar(FI_A_FV);
    let b = k.fvar(FI_B_FV);
    let cv = k.fvar(FI_C_FV);

    // assoc : forall a b c, kerEquiv ((a*b)*c) (a*(b*c))
    let assoc_val = {
        let ab = t_app(k, c.g_op, &[a, b]);
        let ab_c = t_app(k, c.g_op, &[ab, cv]);
        let bc = t_app(k, c.g_op, &[b, cv]);
        let a_bc = t_app(k, c.g_op, &[a, bc]);
        let law = t_app(k, c.g_assoc, &[a, b, cv]);
        let body = t_app(k, c.fc, &[ab_c, a_bc, law]);
        let t = lam_over(k, FI_C_FV, c.gc, body);
        let t = lam_over(k, FI_B_FV, c.gc, t);
        lam_over(k, FI_A_FV, c.gc, t)
    };
    let ident_l_val = {
        let lhs = t_app(k, c.g_op, &[c.g_e, a]);
        let law = k.app(c.g_ident_l, a);
        let body = t_app(k, c.fc, &[lhs, a, law]);
        lam_over(k, FI_A_FV, c.gc, body)
    };
    let ident_r_val = {
        let lhs = t_app(k, c.g_op, &[a, c.g_e]);
        let law = k.app(c.g_ident_r, a);
        let body = t_app(k, c.fc, &[lhs, a, law]);
        lam_over(k, FI_A_FV, c.gc, body)
    };
    let inv_l_val = {
        let ia = k.app(c.g_inv, a);
        let lhs = t_app(k, c.g_op, &[ia, a]);
        let law = k.app(c.g_inv_l, a);
        let body = t_app(k, c.fc, &[lhs, c.g_e, law]);
        lam_over(k, FI_A_FV, c.gc, body)
    };
    let inv_r_val = {
        let ia = k.app(c.g_inv, a);
        let lhs = t_app(k, c.g_op, &[a, ia]);
        let law = k.app(c.g_inv_r, a);
        let body = t_app(k, c.fc, &[lhs, c.g_e, law]);
        lam_over(k, FI_A_FV, c.gc, body)
    };

    let args = [
        c.gc,          // 0 carrier
        equiv_val,     // 1 equiv
        refl_val,      // 2 equivRefl
        symm_val,      // 3 equivSymm
        trans_val,     // 4 equivTrans
        c.g_op,        // 5 op
        op_congr_val,  // 6 opCongr    <- hand-discharged
        c.g_e,         // 7 e
        c.g_inv,       // 8 inv
        inv_congr_val, // 9 invCongr   <- hand-discharged
        assoc_val,     // 10 assoc
        ident_l_val,   // 11 identL
        ident_r_val,   // 12 identR
        inv_l_val,     // 13 invL
        inv_r_val,     // 14 invR
    ];
    let value = structures::mk_instance(k, group, &args);
    let value = close_hom(k, &c, value, true);
    let ty = close_hom(k, &c, c.group_ty, false);

    let name = k.name_str(hom_ns, "quotient");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `AlgS.Hom.quotient_equiv : forall G H f fCongr fMul a b,
/// Iff (AlgS.Group.equiv (quotient ...) a b) (AlgS.Hom.kerEquiv G H f a b)`
/// -- proved by `Iff.intro (fun h => h) (fun h => h)`, so it PASSES only if
/// the record selector on the quotient instance reduces definitionally. A
/// deliberate test, not a convenience lemma.
pub(crate) fn declare_quotient_equiv(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    quotient: NameId,
    ker_equiv: NameId,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    use idx::group::EQUIV;
    let c = hom_ctx(k, group);
    let five = [c.g, c.h, c.f, c.fc, c.fm];
    let q = {
        let t = k.const_(quotient, vec![]);
        t_app(k, t, &five)
    };
    let q_equiv = sel(k, group, EQUIV, q);
    let a = k.fvar(FI_A_FV);
    let b = k.fvar(FI_B_FV);
    let lhs = app2(k, q_equiv, a, b);
    let rhs = {
        let t = k.const_(ker_equiv, vec![]);
        let t = t_app(k, t, &[c.g, c.h, c.f]);
        app2(k, t, a, b)
    };

    let h1 = k.fvar(FI_H1_FV);
    let mp = lam_over(k, FI_H1_FV, lhs, h1);
    let h2 = k.fvar(FI_H2_FV);
    let mpr = lam_over(k, FI_H2_FV, rhs, h2);
    let intro = k.const_(lg.iff_intro, vec![]);
    let body = t_app(k, intro, &[lhs, rhs, mp, mpr]);
    let value = lam_over(k, FI_B_FV, c.gc, body);
    let value = lam_over(k, FI_A_FV, c.gc, value);
    let value = close_hom(k, &c, value, true);

    let iff_c = k.const_(lg.iff, vec![]);
    let concl = app2(k, iff_c, lhs, rhs);
    let ty = pi_over(k, FI_B_FV, c.gc, concl);
    let ty = pi_over(k, FI_A_FV, c.gc, ty);
    let ty = close_hom(k, &c, ty, false);

    let name = k.name_str(hom_ns, "quotient_equiv");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Hom.quotient_equiv_iff_ker : forall G H f fCongr fMul a b,
/// Iff (H.equiv (f a) (f b)) (H.equiv (f (G.op a (G.inv b))) H.e)` --
/// "`a ~ b` in the quotient exactly when `a * b⁻¹` is in the kernel". This
/// is the mathematical content of the first isomorphism theorem that does
/// NOT come for free from the setoid presentation.
pub(crate) fn declare_quotient_equiv_iff_ker(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    inv_unique: NameId,
    map_inv: NameId,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let a = k.fvar(FI_A_FV);
    let b = k.fvar(FI_B_FV);
    let fa = k.app(c.f, a);
    let fb = k.app(c.f, b);
    let inv_b = k.app(c.g_inv, b);
    let f_inv_b = k.app(c.f, inv_b);
    let hi_fb = k.app(c.h_inv, fb);
    let a_invb = t_app(k, c.g_op, &[a, inv_b]);
    let f_a_invb = k.app(c.f, a_invb);
    let prod = t_app(k, c.h_op, &[fa, f_inv_b]);
    let prod_hi = t_app(k, c.h_op, &[fa, hi_fb]);
    let prod_bb = t_app(k, c.h_op, &[fb, hi_fb]);

    let mi = k.const_(map_inv, vec![]);
    let five = [c.g, c.h, c.f, c.fc, c.fm];
    let mi_app = t_app(k, mi, &five);
    let mi_b = k.app(mi_app, b); // H.equiv (f (inv b)) (H.inv (f b))

    let lhs = heq(k, &c, fa, fb);
    let rhs = heq(k, &c, f_a_invb, c.h_e);

    // mp : lhs -> rhs
    let h1 = k.fvar(FI_H1_FV);
    let mp = {
        let w1 = t_app(k, c.fm, &[a, inv_b]);
        let w2 = t_app(k, c.h_op_congr, &[fa, fb, f_inv_b, hi_fb, h1, mi_b]);
        let w12 = htrans(k, &c, f_a_invb, prod, prod_bb, w1, w2);
        let w3 = k.app(c.h_inv_r, fb);
        let body = htrans(k, &c, f_a_invb, prod_bb, c.h_e, w12, w3);
        lam_over(k, FI_H1_FV, lhs, body)
    };

    // mpr : rhs -> lhs
    let h2 = k.fvar(FI_H2_FV);
    let mpr = {
        let w1 = t_app(k, c.fm, &[a, inv_b]);
        let refl_fa = k.app(c.h_refl, fa);
        let w2 = t_app(k, c.h_op_congr, &[fa, fa, f_inv_b, hi_fb, refl_fa, mi_b]);
        let p = htrans(k, &c, f_a_invb, prod, prod_hi, w1, w2);
        let x1 = hsymm(k, &c, f_a_invb, prod_hi, p);
        let x2 = htrans(k, &c, prod_hi, f_a_invb, c.h_e, x1, h2);
        let x3 = k.app(c.h_inv_l, fb);
        let iu = k.const_(inv_unique, vec![]);
        let body = t_app(k, iu, &[c.h, hi_fb, fa, fb, x2, x3]);
        lam_over(k, FI_H2_FV, rhs, body)
    };

    let intro = k.const_(lg.iff_intro, vec![]);
    let body = t_app(k, intro, &[lhs, rhs, mp, mpr]);
    let value = lam_over(k, FI_B_FV, c.gc, body);
    let value = lam_over(k, FI_A_FV, c.gc, value);
    let value = close_hom(k, &c, value, true);

    let iff_c = k.const_(lg.iff, vec![]);
    let concl = app2(k, iff_c, lhs, rhs);
    let ty = pi_over(k, FI_B_FV, c.gc, concl);
    let ty = pi_over(k, FI_A_FV, c.gc, ty);
    let ty = close_hom(k, &c, ty, false);

    let name = k.name_str(hom_ns, "quotient_equiv_iff_ker");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Hom.image_mem : forall G H f fCongr fMul (a : G.carrier),
/// AlgS.Hom.image G H f (f a)` -- the induced map is onto the image.
/// `Exists.intro` at the witness `a` with `H.equivRefl (f a)`; this is the
/// half of "surjective onto the image" that the setoid presentation makes
/// nearly free, and it is reported as such.
pub(crate) fn declare_image_mem(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
    image: NameId,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    let c = hom_ctx(k, group);
    let a = k.fvar(FI_A_FV);
    let fa = k.app(c.f, a);

    let pred = {
        let w = k.fvar(FI_B_FV);
        let fw = k.app(c.f, w);
        let inner = heq(k, &c, fw, fa);
        lam_over(k, FI_B_FV, c.gc, inner)
    };
    let refl_fa = k.app(c.h_refl, fa);
    let intro = k.const_(lg.exists_intro, vec![l1]);
    let body = t_app(k, intro, &[c.gc, pred, a, refl_fa]);
    let value = lam_over(k, FI_A_FV, c.gc, body);
    let value = close_hom(k, &c, value, true);

    let img = k.const_(image, vec![]);
    let concl = {
        let t = t_app(k, img, &[c.g, c.h, c.f]);
        k.app(t, fa)
    };
    let ty = pi_over(k, FI_A_FV, c.gc, concl);
    let ty = close_hom(k, &c, ty, false);

    let name = k.name_str(hom_ns, "image_mem");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `AlgS.Hom.firstIso : forall G H f fCongr fMul,
///   And (forall a b, Iff (Q.equiv a b) (ker (G.op a (G.inv b))))
///       (And (forall a b, H.equiv (f (Q.op a b)) (H.op (f a) (f b)))
///            (forall a, image (f a)))`
/// -- the first isomorphism theorem, assembled. `Q := AlgS.Hom.quotient`.
/// Read: the quotient setoid's equivalence IS the kernel congruence, the
/// induced map is a homomorphism out of it, and it is onto the image; its
/// injectivity is the `mpr` of the first component, which is why no fourth
/// conjunct appears.
#[allow(clippy::too_many_arguments)]
pub(crate) fn declare_first_iso(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    quotient: NameId,
    ker: NameId,
    image: NameId,
    iff_ker: NameId,
    image_mem: NameId,
    hom_ns: NameId,
) -> Result<NameId, KernelError> {
    use idx::group::{EQUIV, OP};
    let c = hom_ctx(k, group);
    let five = [c.g, c.h, c.f, c.fc, c.fm];
    let q = {
        let t = k.const_(quotient, vec![]);
        t_app(k, t, &five)
    };
    let q_equiv = sel(k, group, EQUIV, q);
    let q_op = sel(k, group, OP, q);

    let a = k.fvar(FI_A_FV);
    let b = k.fvar(FI_B_FV);

    // c1 : forall a b, Iff (Q.equiv a b) (ker G H f (G.op a (G.inv b)))
    let c1_ty = {
        let lhs = app2(k, q_equiv, a, b);
        let inv_b = k.app(c.g_inv, b);
        let a_invb = t_app(k, c.g_op, &[a, inv_b]);
        let kc = k.const_(ker, vec![]);
        let kc = t_app(k, kc, &[c.g, c.h, c.f]);
        let rhs = k.app(kc, a_invb);
        let iff_c = k.const_(lg.iff, vec![]);
        let body = app2(k, iff_c, lhs, rhs);
        let t = pi_over(k, FI_B_FV, c.gc, body);
        pi_over(k, FI_A_FV, c.gc, t)
    };
    let c1_val = {
        let t = k.const_(iff_ker, vec![]);
        t_app(k, t, &five)
    };

    // c2 : forall a b, H.equiv (f (Q.op a b)) (H.op (f a) (f b))
    let c2_ty = {
        let ab = app2(k, q_op, a, b);
        let f_ab = k.app(c.f, ab);
        let fa = k.app(c.f, a);
        let fb = k.app(c.f, b);
        let rhs = t_app(k, c.h_op, &[fa, fb]);
        let body = heq(k, &c, f_ab, rhs);
        let t = pi_over(k, FI_B_FV, c.gc, body);
        pi_over(k, FI_A_FV, c.gc, t)
    };
    let c2_val = c.fm;

    // c3 : forall a, image G H f (f a)
    let c3_ty = {
        let fa = k.app(c.f, a);
        let img = k.const_(image, vec![]);
        let t = t_app(k, img, &[c.g, c.h, c.f]);
        let body = k.app(t, fa);
        pi_over(k, FI_A_FV, c.gc, body)
    };
    let c3_val = {
        let t = k.const_(image_mem, vec![]);
        t_app(k, t, &five)
    };

    let and_c = k.const_(lg.and, vec![]);
    let inner_ty = app2(k, and_c, c2_ty, c3_ty);
    let outer_ty = app2(k, and_c, c1_ty, inner_ty);
    let and_intro = k.const_(lg.and_intro, vec![]);
    let inner_val = t_app(k, and_intro, &[c2_ty, c3_ty, c2_val, c3_val]);
    let outer_val = t_app(k, and_intro, &[c1_ty, inner_ty, c1_val, inner_val]);

    let value = close_hom(k, &c, outer_val, true);
    let ty = close_hom(k, &c, outer_ty, false);

    let name = k.name_str(hom_ns, "firstIso");
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
    /// ADR-1592: `AlgS.CommRing.toCommGroupS`, the additive-group forgetful
    /// projection (promotes ADR-1590's test-only `ring_s_additive_group_
    /// value` to a real declared name, widened to `CommGroup`).
    pub comm_ring_to_comm_group_s: NameId,
    /// ADR-1592: `AlgS.CommGroup.toGroupS`, the prefix projection down to a
    /// plain `Group` (needed by `add_left_cancel`/`inv_unique`/`invInv`).
    pub comm_group_to_group_s: NameId,
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
    /// ADR-1592: `AlgS.inv_unique`, the `AlgS.Group`-level uniqueness
    /// theorem (`op b a = e -> op a c = e -> b = c`), mirroring `Alg.
    /// groupInvUnique` exactly.
    pub inv_unique: NameId,
    /// ADR-1592: `AlgS.invInv`, `equiv (inv (inv a)) a` over `AlgS.Group`
    /// -- the theorem `Alg.neg_neg` (stated over `Alg.Group`) now derives
    /// from via `ofAlg`, closing ADR-1590 §3's named scope mismatch.
    pub inv_inv: NameId,
    /// ADR-1592: `AlgS.OrderedRing.ofAlg : Alg.OrderedRing -> AlgS.
    /// OrderedRing`.
    pub ordered_ring_ofalg: NameId,

    // -- ADR-1595 / roadmap W2-8: the first isomorphism theorem over
    // `AlgS.Group`, by the setoid route (no `Quot`, no `Quot.sound`). --
    /// `AlgS.Hom.ker` — the kernel of a homomorphism, as a PREDICATE.
    pub hom_ker: NameId,
    /// `AlgS.Hom.kerEquiv` — the induced equivalence on `G.carrier`.
    pub hom_ker_equiv: NameId,
    /// `AlgS.Hom.image` — the image, as a predicate on `H.carrier`.
    pub hom_image: NameId,
    /// `AlgS.Hom.mapOne` — `H.equiv (f G.e) H.e`.
    pub hom_map_one: NameId,
    /// `AlgS.Hom.mapInv` — `H.equiv (f (G.inv a)) (H.inv (f a))`.
    pub hom_map_inv: NameId,
    /// `AlgS.Hom.kerEquivOpCongr` — congruence obligation 1 of 2, the
    /// quotient's `opCongr` field. A real `Quot` gives this for free.
    pub hom_ker_equiv_op_congr: NameId,
    /// `AlgS.Hom.kerEquivInvCongr` — congruence obligation 2 of 2, the
    /// quotient's `invCongr` field.
    pub hom_ker_equiv_inv_congr: NameId,
    /// `AlgS.Hom.quotient : ... -> AlgS.Group` — the quotient group,
    /// carried as a setoid over the ORIGINAL carrier.
    pub hom_quotient: NameId,
    /// `AlgS.Hom.quotient_equiv` — the quotient's `equiv` selector reduces
    /// to `AlgS.Hom.kerEquiv`, proved by `Iff.intro id id`.
    pub hom_quotient_equiv: NameId,
    /// `AlgS.Hom.quotient_equiv_iff_ker` — `a ~ b` in the quotient exactly
    /// when `a * b⁻¹` is in the kernel.
    pub hom_quotient_equiv_iff_ker: NameId,
    /// `AlgS.Hom.image_mem` — every `f a` is in the image.
    pub hom_image_mem: NameId,
    /// `AlgS.Hom.firstIso` — the assembled first isomorphism theorem.
    pub hom_first_iso: NameId,
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
    let comm_ring_to_comm_group_s = declare_comm_ring_to_comm_group_s(k, st, p)?;
    let comm_group_to_group_s = declare_comm_group_to_group_s(k, st, p)?;

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
    let ordered_ring_ofalg = ofalg::declare_ordered_ring_ofalg(
        k,
        lg,
        l1,
        &alg_st.ordered_ring,
        &st.ordered_ring,
        p.ordered_ring,
    )?;

    let sub = declare_sub_s(k, &st.ring, p.algs)?;
    let sub_self = declare_sub_self(k, &st.ring, sub, p.algs)?;
    let neg_neg = declare_neg_neg(k, &st.ring, p.algs)?;
    let mul_zero = declare_mul_zero(k, &st.ring, p.algs)?;
    let mul_neg_one = declare_mul_neg_one(k, &st.ring, mul_zero, p.algs)?;
    let add_left_cancel = declare_add_left_cancel(k, &st.group, p.algs)?;
    let inv_unique = declare_inv_unique(k, &st.group, p.algs)?;
    let inv_inv = declare_inv_inv(k, &st.group, inv_unique, p.algs)?;

    // ADR-1595 / W2-8: the first isomorphism theorem, setoid route.
    let hom_ns = k.name_str(p.algs, "Hom");
    let hom_ker = declare_hom_ker(k, &st.group, hom_ns)?;
    let hom_ker_equiv = declare_hom_ker_equiv(k, &st.group, hom_ns)?;
    let hom_image = declare_hom_image(k, lg, l1, &st.group, hom_ns)?;
    let hom_map_one = declare_hom_map_one(k, &st.group, add_left_cancel, hom_ns)?;
    let hom_map_inv = declare_hom_map_inv(k, &st.group, inv_unique, hom_map_one, hom_ns)?;
    let hom_ker_equiv_op_congr = declare_ker_equiv_op_congr(k, &st.group, hom_ns)?;
    let hom_ker_equiv_inv_congr = declare_ker_equiv_inv_congr(k, &st.group, hom_map_inv, hom_ns)?;
    let hom_quotient = declare_hom_quotient(
        k,
        &st.group,
        hom_ker_equiv_op_congr,
        hom_ker_equiv_inv_congr,
        hom_ns,
    )?;
    let hom_quotient_equiv =
        declare_quotient_equiv(k, lg, &st.group, hom_quotient, hom_ker_equiv, hom_ns)?;
    let hom_quotient_equiv_iff_ker =
        declare_quotient_equiv_iff_ker(k, lg, &st.group, inv_unique, hom_map_inv, hom_ns)?;
    let hom_image_mem = declare_image_mem(k, lg, l1, &st.group, hom_image, hom_ns)?;
    let hom_first_iso = declare_first_iso(
        k,
        lg,
        &st.group,
        hom_quotient,
        hom_ker,
        hom_image,
        hom_quotient_equiv_iff_ker,
        hom_image_mem,
        hom_ns,
    )?;

    let _ = alg_p;

    Ok(StructuresSExtraNames {
        comm_ring_to_ring_s,
        comm_ring_to_comm_group_s,
        comm_group_to_group_s,
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
        inv_unique,
        inv_inv,
        ordered_ring_ofalg,
        hom_ker,
        hom_ker_equiv,
        hom_image,
        hom_map_one,
        hom_map_inv,
        hom_ker_equiv_op_congr,
        hom_ker_equiv_inv_congr,
        hom_quotient,
        hom_quotient_equiv,
        hom_quotient_equiv_iff_ker,
        hom_image_mem,
        hom_first_iso,
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
            ("OrderedRing", 29),
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
            st.ordered_ring.field_count(),
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
            &st.ordered_ring,
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
            extra.comm_ring_to_comm_group_s,
            extra.comm_group_to_group_s,
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
            extra.inv_unique,
            extra.inv_inv,
            extra.ordered_ring_ofalg,
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
            extra.comm_ring_to_comm_group_s,
            extra.comm_group_to_group_s,
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
            extra.inv_unique,
            extra.inv_inv,
            extra.ordered_ring_ofalg,
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

    /// ADR-1592 deliverable 2: `AlgS.invInv` instantiated at ℤ through
    /// `ofAlg` (`AlgS.Group.ofAlg(Int.addGroup)`), concrete and symbolic.
    /// `Int` has no named `neg_neg`/`invInv` theorem (ADR-1584 §3: only a
    /// private helper in `int_prelude/gcd.rs`), so this test confirms only
    /// well-typedness, like `AlgS.neg_neg`'s and `AlgS.mul_neg_one`'s own
    /// Int controls.
    #[test]
    fn inv_inv_instantiated_at_int_through_ofalg_concrete_and_symbolic() {
        use crate::rat_prelude::build_rat_prelude;
        const A_FV: u64 = 24_050;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;

        let int_add_group_alg = k.const_(rp.algebra.int_add_group, vec![]);
        let group_ofalg = k.const_(extra.group_ofalg, vec![]);
        let int_group_s = k.app(group_ofalg, int_add_group_alg);
        let inv_inv_c = k.const_(extra.inv_inv, vec![]);
        let applied = k.app(inv_inv_c, int_group_s);
        let int_ty = k.const_(rp.int.z, vec![]);

        let zero_c = k.const_(rp.int.zero, vec![]);
        let applied_zero = k.app(applied, zero_c);
        assert!(
            k.infer(applied_zero).is_ok(),
            "AlgS.invInv applied at Int's Group projection must infer a type at Int.zero"
        );

        let a = k.fvar(A_FV);
        let applied_a = k.app(applied, a);
        let closed = lam_over(&mut k, A_FV, int_ty, applied_a);
        assert!(
            k.infer(closed).is_ok(),
            "AlgS.invInv closed at Int's Group projection must infer a type"
        );
    }

    /// ADR-1592: `AlgS.inv_unique` instantiated at ℤ through `ofAlg`,
    /// concrete and symbolic (the uniqueness lemma `invInv` is built from).
    #[test]
    fn inv_unique_instantiated_at_int_through_ofalg_concrete_and_symbolic() {
        use crate::rat_prelude::build_rat_prelude;
        const A_FV: u64 = 24_060;
        const B_FV: u64 = 24_061;
        const C_FV: u64 = 24_062;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;

        let int_add_group_alg = k.const_(rp.algebra.int_add_group, vec![]);
        let group_ofalg = k.const_(extra.group_ofalg, vec![]);
        let int_group_s = k.app(group_ofalg, int_add_group_alg);
        let inv_unique_c = k.const_(extra.inv_unique, vec![]);
        let int_ty = k.const_(rp.int.z, vec![]);

        let zero_c = k.const_(rp.int.zero, vec![]);
        let applied_zero = {
            let e1 = k.app(inv_unique_c, int_group_s);
            let e2 = k.app(e1, zero_c);
            let e3 = k.app(e2, zero_c);
            k.app(e3, zero_c)
        };
        assert!(
            k.infer(applied_zero).is_ok(),
            "AlgS.inv_unique applied at Int's Group projection must infer a type at \
             (Int.zero,Int.zero,Int.zero)"
        );

        let a = k.fvar(A_FV);
        let b = k.fvar(B_FV);
        let c = k.fvar(C_FV);
        let generic_applied = {
            let e1 = k.app(inv_unique_c, int_group_s);
            let e2 = k.app(e1, a);
            let e3 = k.app(e2, b);
            k.app(e3, c)
        };
        let closed = {
            let v = generic_applied;
            let v = lam_over(&mut k, C_FV, int_ty, v);
            let v = lam_over(&mut k, B_FV, int_ty, v);
            lam_over(&mut k, A_FV, int_ty, v)
        };
        assert!(
            k.infer(closed).is_ok(),
            "AlgS.inv_unique closed at Int's Group projection must infer a type"
        );
    }

    /// ADR-1592: `AlgS.add_left_cancel` reached via the NEW `AlgS.CommRing.
    /// toCommGroupS`/`AlgS.CommGroup.toGroupS` projection pair (rather than
    /// `AlgS.Group.ofAlg` directly) must still be `def_eq` to `Int.
    /// add_left_cancel`'s own declared type -- confirms the two new
    /// projections compose to the SAME additive group `AlgS.Group.ofAlg`
    /// already reaches, not merely that SOMETHING type-checks (a
    /// projection to a wrong/opaque carrier would still type-check as a
    /// `Group`, per `kernel-proof-engineering.md`'s warning -- `def_eq`
    /// against a real Int theorem is the discriminating check).
    #[test]
    fn add_left_cancel_instantiated_at_int_through_comm_ring_to_comm_group_s_matches_int_add_left_cancel_type()
     {
        use crate::rat_prelude::build_rat_prelude;
        const A_FV: u64 = 24_070;
        const B_FV: u64 = 24_071;
        const C_FV: u64 = 24_072;
        let mut k = Kernel::new();
        let rp = build_rat_prelude(&mut k).expect("rat prelude must build");
        let np = rp.int.nat;
        let extra = np.structures_s_extra;

        let int_comm_ring_alg = k.const_(rp.algebra.int_comm_ring, vec![]);
        let comm_ring_ofalg = k.const_(extra.comm_ring_ofalg, vec![]);
        let int_comm_ring_s = k.app(comm_ring_ofalg, int_comm_ring_alg);

        let to_comm_group_s = k.const_(extra.comm_ring_to_comm_group_s, vec![]);
        let int_comm_group_s = k.app(to_comm_group_s, int_comm_ring_s);
        let to_group_s = k.const_(extra.comm_group_to_group_s, vec![]);
        let int_group_s = k.app(to_group_s, int_comm_group_s);

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
        let generic_ty = k.infer(generic_closed).expect(
            "AlgS.add_left_cancel closed at Int's CommRing->CommGroupS->GroupS projection \
             must type-check",
        );

        let hand = k.const_(rp.int.add_left_cancel, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_left_cancel must exist");

        assert!(
            k.def_eq(generic_ty, hand_ty),
            "AlgS.add_left_cancel via CommRing.toCommGroupS/CommGroup.toGroupS must have the \
             SAME TYPE as Int.add_left_cancel"
        );
    }
}

/// ADR-1595 / roadmap W2-8. The measurement suite for the first isomorphism
/// theorem built by the SETOID route. Every assertion here reads the KERNEL,
/// never a rendered name or a source comment.
#[cfg(test)]
mod first_iso_tests {
    use super::*;
    use crate::build_logic_prelude;
    use crate::nat_prelude::structures as algeq;

    fn build_extra(k: &mut Kernel) -> StructuresSExtraNames {
        let logic = build_logic_prelude(k).expect("logic prelude must build");
        let alg_p = algeq::intern_structures_names(k);
        let alg_st = algeq::declare_structures_all(k, &alg_p, &logic).expect("Alg spine builds");
        let p = intern_structures_s_names(k);
        let st = declare_structures_s_all(k, &p, &logic).expect("AlgS spine builds");
        declare_structures_s_extra(k, &logic, &p, &st, &alg_p, &alg_st)
            .expect("AlgS extras + the first isomorphism theorem must admit")
    }

    /// The twelve `AlgS.Hom.*` declarations, in dependency order. Derived
    /// from the names struct, not from a literal list of strings, so a
    /// renamed or dropped declaration breaks the test rather than the test's
    /// idea of what exists.
    fn first_iso_names(extra: &StructuresSExtraNames) -> [NameId; 12] {
        [
            extra.hom_ker,
            extra.hom_ker_equiv,
            extra.hom_image,
            extra.hom_map_one,
            extra.hom_map_inv,
            extra.hom_ker_equiv_op_congr,
            extra.hom_ker_equiv_inv_congr,
            extra.hom_quotient,
            extra.hom_quotient_equiv,
            extra.hom_quotient_equiv_iff_ker,
            extra.hom_image_mem,
            extra.hom_first_iso,
        ]
    }

    #[test]
    fn first_isomorphism_theorem_admits_by_the_setoid_route() {
        let mut k = Kernel::new();
        let extra = build_extra(&mut k);
        for name in first_iso_names(&extra) {
            assert!(
                k.environment().get(name).is_some(),
                "declaration missing from the environment"
            );
        }
    }

    /// **The headline claim.** Read from `Kernel::axiom_footprint`, which is
    /// the transitive axiom closure of the checked declaration -- not from a
    /// name, a doc comment, or the absence of an `Axiom` in this file.
    #[test]
    fn first_isomorphism_theorem_is_axiom_free() {
        let mut k = Kernel::new();
        let extra = build_extra(&mut k);
        for name in first_iso_names(&extra) {
            let footprint = k.axiom_footprint(name);
            assert!(
                footprint.is_empty(),
                "axiom footprint must be empty, got {} entries",
                footprint.len()
            );
        }
    }

    /// The quotient is a genuine `AlgS.Group` VALUE, and its `equiv` field
    /// is the kernel congruence. `AlgS.Hom.quotient_equiv` is proved by
    /// `Iff.intro (fun h => h) (fun h => h)`, so its admission is exactly
    /// the statement that the record selector on the quotient instance
    /// reduces definitionally to `AlgS.Hom.kerEquiv`. The assertion here is
    /// that the declaration is a `Theorem` (i.e. the kernel checked that
    /// proof), so the test cannot pass on a stub.
    #[test]
    fn the_quotients_equiv_reduces_to_the_kernel_congruence() {
        let mut k = Kernel::new();
        let extra = build_extra(&mut k);
        let decl = k
            .environment()
            .get(extra.hom_quotient_equiv)
            .expect("quotient_equiv must exist")
            .clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "quotient_equiv must be a checked Theorem"
        );
        let q = k
            .environment()
            .get(extra.hom_quotient)
            .expect("quotient must exist")
            .clone();
        assert!(
            matches!(q, Declaration::Definition { .. }),
            "the quotient must be a Definition producing an AlgS.Group"
        );
    }

    /// **Negative control for the congruence obligation.** Rebuild the
    /// quotient instance with field 6 (`opCongr`) supplied by the SOURCE
    /// group's own `opCongr` -- the congruence for `G.equiv`, not for the
    /// coarser kernel congruence. The kernel must REJECT it. If this
    /// admitted, `AlgS.Hom.kerEquivOpCongr` would not be load-bearing and
    /// the "two hand-discharged congruence obligations" measurement in
    /// ADR-1595 would be wrong.
    #[test]
    fn the_quotient_is_rejected_without_the_kernel_congruence_proof() {
        use idx::group::OP_CONGR;
        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k).expect("logic prelude must build");
        let alg_p = algeq::intern_structures_names(&mut k);
        let alg_st =
            algeq::declare_structures_all(&mut k, &alg_p, &logic).expect("Alg spine builds");
        let p = intern_structures_s_names(&mut k);
        let st = declare_structures_s_all(&mut k, &p, &logic).expect("AlgS spine builds");
        let extra = declare_structures_s_extra(&mut k, &logic, &p, &st, &alg_p, &alg_st)
            .expect("extras must admit");

        let group = &st.group;
        let c = hom_ctx(&mut k, group);
        // Rebuild the honest quotient's fields, then swap slot 6.
        let equiv_val = {
            let a = k.fvar(FI_A_FV);
            let b = k.fvar(FI_B_FV);
            let fa = k.app(c.f, a);
            let fb = k.app(c.f, b);
            let body = heq(&mut k, &c, fa, fb);
            let t = lam_over(&mut k, FI_B_FV, c.gc, body);
            lam_over(&mut k, FI_A_FV, c.gc, t)
        };
        let refl_val = {
            let a = k.fvar(FI_A_FV);
            let fa = k.app(c.f, a);
            let body = k.app(c.h_refl, fa);
            lam_over(&mut k, FI_A_FV, c.gc, body)
        };
        let symm_val = {
            let a = k.fvar(FI_A_FV);
            let b = k.fvar(FI_B_FV);
            let fa = k.app(c.f, a);
            let fb = k.app(c.f, b);
            let hyp = heq(&mut k, &c, fa, fb);
            let hv = k.fvar(FI_H1_FV);
            let body = hsymm(&mut k, &c, fa, fb, hv);
            let t = lam_over(&mut k, FI_H1_FV, hyp, body);
            let t = lam_over(&mut k, FI_B_FV, c.gc, t);
            lam_over(&mut k, FI_A_FV, c.gc, t)
        };
        let trans_val = {
            let a = k.fvar(FI_A_FV);
            let b = k.fvar(FI_B_FV);
            let cv = k.fvar(FI_C_FV);
            let fa = k.app(c.f, a);
            let fb = k.app(c.f, b);
            let fcv = k.app(c.f, cv);
            let hyp1 = heq(&mut k, &c, fa, fb);
            let hyp2 = heq(&mut k, &c, fb, fcv);
            let h1 = k.fvar(FI_H1_FV);
            let h2 = k.fvar(FI_H2_FV);
            let body = htrans(&mut k, &c, fa, fb, fcv, h1, h2);
            let t = lam_over(&mut k, FI_H2_FV, hyp2, body);
            let t = lam_over(&mut k, FI_H1_FV, hyp1, t);
            let t = lam_over(&mut k, FI_C_FV, c.gc, t);
            let t = lam_over(&mut k, FI_B_FV, c.gc, t);
            lam_over(&mut k, FI_A_FV, c.gc, t)
        };
        let five = [c.g, c.h, c.f, c.fc, c.fm];
        let inv_congr_val = {
            let t = k.const_(extra.hom_ker_equiv_inv_congr, vec![]);
            t_app(&mut k, t, &five)
        };
        // THE MUTATION: `G.opCongr`, which proves congruence for `G.equiv`,
        // in the slot that needs congruence for the kernel congruence.
        let bogus_op_congr = sel(&mut k, group, OP_CONGR, c.g);

        let a = k.fvar(FI_A_FV);
        let b = k.fvar(FI_B_FV);
        let cv = k.fvar(FI_C_FV);
        let assoc_val = {
            let ab = t_app(&mut k, c.g_op, &[a, b]);
            let ab_c = t_app(&mut k, c.g_op, &[ab, cv]);
            let bc = t_app(&mut k, c.g_op, &[b, cv]);
            let a_bc = t_app(&mut k, c.g_op, &[a, bc]);
            let law = t_app(&mut k, c.g_assoc, &[a, b, cv]);
            let body = t_app(&mut k, c.fc, &[ab_c, a_bc, law]);
            let t = lam_over(&mut k, FI_C_FV, c.gc, body);
            let t = lam_over(&mut k, FI_B_FV, c.gc, t);
            lam_over(&mut k, FI_A_FV, c.gc, t)
        };
        let ident_l_val = {
            let lhs = t_app(&mut k, c.g_op, &[c.g_e, a]);
            let law = k.app(c.g_ident_l, a);
            let body = t_app(&mut k, c.fc, &[lhs, a, law]);
            lam_over(&mut k, FI_A_FV, c.gc, body)
        };
        let ident_r_val = {
            let lhs = t_app(&mut k, c.g_op, &[a, c.g_e]);
            let law = k.app(c.g_ident_r, a);
            let body = t_app(&mut k, c.fc, &[lhs, a, law]);
            lam_over(&mut k, FI_A_FV, c.gc, body)
        };
        let inv_l_val = {
            let ia = k.app(c.g_inv, a);
            let lhs = t_app(&mut k, c.g_op, &[ia, a]);
            let law = k.app(c.g_inv_l, a);
            let body = t_app(&mut k, c.fc, &[lhs, c.g_e, law]);
            lam_over(&mut k, FI_A_FV, c.gc, body)
        };
        let inv_r_val = {
            let ia = k.app(c.g_inv, a);
            let lhs = t_app(&mut k, c.g_op, &[a, ia]);
            let law = k.app(c.g_inv_r, a);
            let body = t_app(&mut k, c.fc, &[lhs, c.g_e, law]);
            lam_over(&mut k, FI_A_FV, c.gc, body)
        };

        let args = [
            c.gc,
            equiv_val,
            refl_val,
            symm_val,
            trans_val,
            c.g_op,
            bogus_op_congr, // <- the mutation
            c.g_e,
            c.g_inv,
            inv_congr_val,
            assoc_val,
            ident_l_val,
            ident_r_val,
            inv_l_val,
            inv_r_val,
        ];
        let value = structures::mk_instance(&mut k, group, &args);
        let value = close_hom(&mut k, &c, value, true);
        let ty = close_hom(&mut k, &c, c.group_ty, false);
        let name = k.name_str(p.algs, "HomQuotientMutant");
        let outcome = k.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        });
        assert!(
            outcome.is_err(),
            "the quotient must NOT admit with the source group's own opCongr \
             in the kernel-congruence slot -- if it does, \
             AlgS.Hom.kerEquivOpCongr is not load-bearing"
        );
    }

    /// Print the rendered types of every `AlgS.Hom.*` declaration. Run with
    /// `--nocapture` to read them; the assertion is that each type actually
    /// mentions the `AlgS.Group` record, so the test cannot pass vacuously
    /// on an empty render.
    #[test]
    fn first_isomorphism_theorem_types_render() {
        let mut k = Kernel::new();
        let extra = build_extra(&mut k);
        for name in first_iso_names(&extra) {
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
                rendered.contains("AlgS.Group"),
                "rendered type must mention AlgS.Group"
            );
        }
    }
}
