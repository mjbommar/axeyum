//! ADR-1592: a small bridge from `creal/*.rs`'s per-site order-chain hand
//! proofs to `linarith::generic::prove_s`, over `AlgS.Rat.orderedRingS`
//! (`nat_prelude::structures_setoid`/`rat_prelude::ordered_ring_ext_s`).
//! Two shapes, each proved ONCE here (by CITING the generic producer, not
//! by hand) and reused at every retirement site this ADR names, instead of
//! each site hand-building its own `le_refl`+`add_le_add`(+`add_zero`)
//! chain independently.
//!
//! Both routes are `AlgS.Rat.orderedRingS`-specific (not `CReal`-carrier),
//! because the sites they replace are themselves `Rat`-level helpers that
//! happen to live in a `creal/*.rs` module (feeding a larger `CReal`
//! construction) — `linarith::generic::prove_s` reaches whichever carrier
//! it is pointed at, and this module points it at the one these sites
//! actually need.

use crate::Kernel;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::linarith::generic::prove_s;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::sel;
use crate::nat_prelude::structures_setoid::idx::ordered_ring as oidx;
use crate::rat_prelude::RatPrelude;

use super::CRealPrelude;

/// `AlgS.Rat.orderedRingS` as a term, plus the `le`/`add`/`zero` selectors
/// off it -- **selector applications, not the bare `Rat.*` constants**,
/// even though the two are `def_eq`. `linarith::generic::Problem`'s
/// `ofnat_numeral` recognises a literal zero by SYNTACTIC `ExprId`
/// equality against its own `self.zero` (a selector application off the
/// SAME ring term), not `def_eq` — so a hypothesis/goal built from the
/// bare `Rat.zero` constant instead would silently fail to parse as the
/// constant `0` and the certificate search would decline. Measured, not
/// theorised: the first version of this module used `Rat.zero` directly
/// and every `rat_le_add_right` call inside a real prelude build panicked
/// with `Decline::NoCertificate`.
struct RatRingS {
    ring: ExprId,
    le: ExprId,
    add: ExprId,
    zero: ExprId,
}

fn rat_ring_s(k: &mut Kernel, rp: &RatPrelude) -> RatRingS {
    let rn = &rp.int.nat.structures_s.ordered_ring;
    let ring = k.const_(rp.ordered_ring_ext_s.rat_ordered_ring_s, vec![]);
    let le = sel(k, rn, oidx::LE, ring);
    let add = sel(k, rn, oidx::ADD, ring);
    let zero = sel(k, rn, oidx::ZERO, ring);
    RatRingS {
        ring,
        le,
        add,
        zero,
    }
}

/// `Rat.le x (Rat.add x y)`, given `hy : Rat.le Rat.zero y` — the shape
/// four `creal/*.rs` modules each hand-built independently before this ADR
/// (`integral::le_add_nonneg_right`, `integral::rle_add_right`,
/// `sqrt::rat_le_add_nonneg`, `supremum::rat_le_add_right`), each via
/// `le_refl`+`add_le_add`+`add_zero`. Routed through `linarith::generic::
/// prove_s` instead.
pub(super) fn rat_le_add_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    hy: ExprId,
) -> ExprId {
    let rp = p.rat;
    let l1 = d.level_one();
    let k = d.kernel();
    let rr = rat_ring_s(k, &rp);
    let h_ty = {
        let e1 = k.app(rr.le, rr.zero);
        k.app(e1, y)
    };
    let xy = {
        let e1 = k.app(rr.add, x);
        k.app(e1, y)
    };
    let goal = {
        let e1 = k.app(rr.le, x);
        k.app(e1, xy)
    };
    prove_s(
        k,
        &rp.int.nat.logic,
        l1,
        &rp.int.nat.structures_s,
        &rp.ordered_ring_ext_s,
        &rp.int.nat,
        rr.ring,
        None,
        &[(h_ty, hy)],
        goal,
    )
    .expect("linarith::generic (setoid) must derive x<=x+y from 0<=y over AlgS.Rat.orderedRingS")
}

/// `Rat.le (Rat.add a c) (Rat.add b e)`, given `hm : Rat.le a b`, `hn :
/// Rat.le c e` — the shape `completeness::moduli_shift_le` hand-built
/// before this ADR via one direct `Rat.add_le_add` citation. Routed
/// through `linarith::generic::prove_s` instead.
pub(super) fn rat_add_le_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
    hm: ExprId,
    hn: ExprId,
) -> ExprId {
    let rp = p.rat;
    let l1 = d.level_one();
    let k = d.kernel();
    let rr = rat_ring_s(k, &rp);
    let h1_ty = {
        let e1 = k.app(rr.le, a);
        k.app(e1, b)
    };
    let h2_ty = {
        let e1 = k.app(rr.le, c);
        k.app(e1, e)
    };
    let ac = {
        let e1 = k.app(rr.add, a);
        k.app(e1, c)
    };
    let be = {
        let e1 = k.app(rr.add, b);
        k.app(e1, e)
    };
    let goal = {
        let e1 = k.app(rr.le, ac);
        k.app(e1, be)
    };
    prove_s(
        k,
        &rp.int.nat.logic,
        l1,
        &rp.int.nat.structures_s,
        &rp.ordered_ring_ext_s,
        &rp.int.nat,
        rr.ring,
        None,
        &[(h1_ty, hm), (h2_ty, hn)],
        goal,
    )
    .expect(
        "linarith::generic (setoid) must derive Rat.add_le_add's shape over AlgS.Rat.orderedRingS",
    )
}
