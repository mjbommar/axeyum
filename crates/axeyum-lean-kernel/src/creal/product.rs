//! **`CReal.mul`**, and the five of the 22 ordered-ring laws that follow from
//! it directly (ADR-0512 phase R2, continued).
//!
//! ## The one thing a product needs that a sum does not
//!
//! `CReal.add` samples at Bishop's *fixed* shift `2n+1`, because adding two
//! regular sequences doubles the error and sampling twice as deep halves each
//! modulus back. Multiplying does not degrade the modulus by a constant: the
//! error of `x·y` at two indices is
//!
//! ```text
//! x_i·y_i − x_j·y_j = x_i·(y_i − y_j) + (x_i − x_j)·y_j
//! ```
//!
//! so it is bounded by `(|x| + |y|) · (1/(i+1) + 1/(j+1))` — and the factor
//! `|x| + |y|` depends on the two reals. The sampling index therefore has to
//! depend on them too, and that is the whole difficulty: **`CReal.mul` needs a
//! canonical bound on a representative, computed from the representative.**
//!
//! ## Why the fixed modulus makes that bound cheap, not expensive
//!
//! The usual story — Bishop's, and Mathlib's `CauSeq` after him — is that the
//! bound comes out of the Cauchy *existential* modulus, so it has to be
//! extracted before it can be used. With ADR-0512's fixed modulus there is
//! nothing to extract. Regularity at `n = 0` says `|x_m − x_0| ≤ 1/(m+1) + 1`
//! for **every** `m` outright, and `1/(m+1) ≤ 1` is
//! [`Rat.natDivSucc_le_one`](crate::RatPrelude::nat_div_succ_le_one), so
//!
//! ```text
//! |x_m| ≤ |x_0| + 2      for every m,
//! ```
//!
//! with no choice, no search and no extraction. The one genuinely missing piece
//! was a **ℕ-valued** magnitude, and that is
//! [`Rat.bounds_num`](crate::RatPrelude::bounds_num): `|q| ≤ |num q|`, two
//! `Int` facts about `Int.natAbs` and one cross-multiplication. So
//! [`CReal.bound`](super::CRealPrelude::bound) is a *projection*
//! — `natAbs (num (seq x 0)) + 1` — and not a choice principle.
//!
//! ## The index, and why the estimate is exact
//!
//! With `Kx = bound x + 1` and `Ky = bound y + 1` the canonical bounds are
//! `Kx/1` and `Ky/1`, and [`CReal.mulShift`](super::CRealPrelude::mul_shift) is
//! `c := bound x + bound y + 1`, so that `c + 1 = Kx + Ky` **without any
//! ℕ-subtraction**. The representative is
//!
//! ```text
//! (x·y)_n := x_{(c+1)·n + c} · y_{(c+1)·n + c}
//! ```
//!
//! and `(c+1)·n + c` is exactly the index at which
//! [`Rat.natDivSucc_scale`](crate::RatPrelude::nat_div_succ_scale) reads
//! `(c+1)/((c+1)·n + c + 1)` as `1/(n+1)`. The estimate then closes with **no
//! slack at all**: the four terms
//! `Kx/(A+1) + Kx/(B+1) + Ky/(A+1) + Ky/(B+1)` fuse in the numerator to
//! `(Kx+Ky)/(A+1) + (Kx+Ky)/(B+1)`, and each of those *is* `1/(m+1)`,
//! `1/(n+1)` — the regularity bound, on the nose.
//!
//! `natDivSucc` is still never needed antitone in its index. Every comparison
//! of two `natDivSucc`s here happens at one denominator, through
//! `natDivSucc_scale` and `natDivSucc_le_add_left`, exactly as `add_zero` and
//! `add_assoc` did with the fixed shift.
//!
//! ## `mul_assoc`, `left_distrib`, `mul_le_mul` and `mul_congr`, and why the
//! discrimination witness still matters for the other five
//!
//! An earlier pass of this module left `mul_assoc`, `left_distrib`,
//! `mul_le_mul_of_nonneg_left` and `mul_congr` unproved: all compare two
//! products sampled at *different* indices — `mul x (add y z)` and
//! `add (mul x y) (mul x z)` do not agree on any index and their shifts are
//! not even equal as naturals — so each needs the arbitrary-third-index
//! estimate `Equiv.trans` runs on, plus the Archimedean lemma. That estimate
//! is now [`declare_equiv_of_bounded`], immediately below, and
//! [`regular_between`]/[`cross_gap`]/[`product_gap`] are the reusable pieces
//! it turned into; all four laws are declared by [`declare_product`] above.
//! [`convergence`](super::convergence)'s `converges_mul` reuses
//! `regular_between` and `product_gap` directly (widened to `pub(super)`)
//! rather than re-deriving them.
//!
//! Of the five that were here from the start, three —
//! [`mul_zero`](super::CRealPrelude::mul_zero),
//! [`sq_nonneg`](super::CRealPrelude::sq_nonneg) and
//! [`mul_comm`](super::CRealPrelude::mul_comm) — hold, footprint-free, of the
//! degenerate product `fun _ _ => zero`. That is the same trap the strict order
//! walked into, where six of seven laws only *consumed* a `lt` and so held of
//! the empty relation. The answer is the same:
//! [`of_rat_mul`](super::CRealPrelude::of_rat_mul) pins `mul` on the embedded
//! rationals — it is a ring homomorphism statement, not a property — and
//! [`not_equiv_mul_one_one_zero`](super::CRealPrelude::not_equiv_mul_one_one_zero)
//! exhibits, by computation, a product the setoid separates from `zero`. Delete
//! either and every other row still passes.

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::abs::{abs_num_nat_abs_eq, mul_self_abs_rat, rabs};
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, num, radd, rat_eq_rewrite, rchain, rcongr, rle, rmul, rneg,
    rone, rrefl, rsymm, rtrans, rzero,
};

use super::{
    CRealPrelude, DERIVED_HEIGHT, creal_ty, div_succ, embed, equiv, halves, modulus, sample,
    weaken, within,
};

/// Admit `CReal.bound`, `CReal.mulShift`, `CReal.mul` and the five laws.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_product(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_bound(d, p)?;
    declare_bound_within(d, p)?;
    declare_mul(d, p)?;
    declare_equiv_of_bounded(d, p)?;
    declare_mul_congr(d, p)?;
    declare_left_distrib(d, p)?;
    declare_mul_assoc(d, p)?;
    declare_of_rat_mul(d, p)?;
    declare_pointwise_laws(d, p)?;
    declare_neg_mul_neg(d, p)?;
    declare_mul_one(d, p)?;
    declare_nonneg_laws(d, p)?;
    declare_mul_le_mul(d, p)?;
    declare_discrimination(d, p)
}

// --- term builders ----------------------------------------------------------

/// `Rat.natDivSucc k j` with a **symbolic** numerator — [`div_succ`] only takes
/// literals, and every bound here is scaled by a `CReal.bound`.
fn div_succ_at(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `CReal.bound x`.
fn bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.bound, &[x])
}

/// `CReal.bound x + 1`, the numerator of the canonical bound.
fn magnitude_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let base = bound_of(d, p, x);
    d.succ(base)
}

/// `(CReal.bound x + 1)/1`, the canonical bound itself.
fn bound_value(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let k = magnitude_of(d, p, x);
    let zero_nat = d.num(0);
    div_succ_at(d, p, k, zero_nat)
}

/// `CReal.mulShift x y` — the `c` of `(c+1)·n + c`.
pub(super) fn mul_shift(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul_shift, &[x, y])
}

/// `(c+1)·n + c`, the index `CReal.mul` samples at.
pub(super) fn mul_index(d: &mut IntDev<'_>, c: ExprId, n: ExprId) -> ExprId {
    let factor = d.succ(c);
    let scaled = NatOps::mul(d, factor, n);
    NatOps::add(d, scaled, c)
}

/// `CReal.mul x y`.
pub(super) fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

/// `CReal.add x y`.
fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

/// `Rat.le (natDivSucc k ((c+1)·n + c)) (natDivSucc k n)` — a bound read at a
/// product index, brought back to `n`.
pub(super) fn index_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    c: ExprId,
    n: ExprId,
) -> ExprId {
    d.lemma(p.rat.nat_div_succ_le_scaled, &[k, c, n])
}

/// The same at a **composed** index `(a+1)·((b+1)·n + b) + a`.
///
/// `Rat.nat_index_compose` says that shape *is* a product index in `n`, so this
/// is one rewrite followed by [`index_le`]. Bishop's additive shift `2n+1` is
/// the `a = 1` case, which is why `CReal.add` nested inside `CReal.mul` needs
/// no arithmetic of its own.
pub(super) fn composed_index_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let rat = p.rat;
    let inner = mul_index(d, b, n);
    let outer = mul_index(d, a, inner);
    let composed = {
        let factor = d.succ(a);
        let scaled = NatOps::mul(d, factor, b);
        NatOps::add(d, scaled, a)
    };
    let flattened = mul_index(d, composed, n);
    let base = index_le(d, p, k, composed, n);
    let forward = d.lemma(rat.nat_index_compose, &[a, b, n]);
    let back = NatOps::symm(d, outer, flattened, forward);
    let shallow = div_succ_at(d, p, k, n);
    nat_rewrite_prop(d, flattened, outer, back, base, &|d, t| {
        let deep = div_succ_at(d, p, k, t);
        rle(d, rat, deep, shallow)
    })
}

/// `Within r (natDivSucc a n)` and `Within s (natDivSucc b n)` give
/// `Within (r + s) (natDivSucc (a + b) n)`.
///
/// Every crude estimate below is a sum of terms already read back at `n`, so
/// this is the only combining step any of them needs: `bounds_add` followed by
/// `natDivSucc_add`, with the numerators doing the bookkeeping.
pub(super) fn fuse_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    left: ExprId,
    left_numerator: ExprId,
    right: ExprId,
    right_numerator: ExprId,
    n: ExprId,
    left_proof: ExprId,
    right_proof: ExprId,
) -> ExprId {
    let rat = p.rat;
    let left_bound = div_succ_at(d, p, left_numerator, n);
    let right_bound = div_succ_at(d, p, right_numerator, n);
    let (ll, lu) = halves(d, p, left, left_bound, left_proof);
    let (rl, ru) = halves(d, p, right, right_bound, right_proof);
    let combined = d.lemma(
        rat.bounds_add,
        &[left, left_bound, right, right_bound, ll, lu, rl, ru],
    );
    let summed = radd(d, left_bound, right_bound);
    let total = NatOps::add(d, left_numerator, right_numerator);
    let target = div_succ_at(d, p, total, n);
    let fuse = d.lemma(rat.nat_div_succ_add, &[left_numerator, right_numerator, n]);
    let quantity = radd(d, left, right);
    rat_eq_rewrite(d, summed, target, fuse, combined, &|d, t| {
        within(d, p, quantity, t)
    })
}

/// `Within (seq u i − seq u j) (natDivSucc 2 n)`, given for each of `i` and `j`
/// a proof that its modulus is at most `1/(n+1)`.
///
/// **This is where the crude estimates get their slack.** The exact bookkeeping
/// `CReal.mul`'s own regularity achieves is not available across two different
/// shifts, and it does not have to be:
/// [`declare_equiv_of_bounded`] accepts any constant.
pub(super) fn regular_between(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    high: ExprId,
    low: ExprId,
    high_le: ExprId,
    low_le: ExprId,
    n: ExprId,
) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let quantity = {
        let a = sample(d, p, u, high);
        let b = sample(d, p, u, low);
        rsub(d, rat, a, b)
    };
    let spread = modulus(d, p, high, low);
    let witness = d.lemma(p.regular, &[u, high, low]);
    let high_atom = div_succ(d, p, 1, high);
    let low_atom = div_succ(d, p, 1, low);
    let shallow = div_succ(d, p, 1, n);
    let grown = d.lemma(
        rat.add_le_add,
        &[high_atom, shallow, low_atom, shallow, high_le, low_le],
    );
    let doubled = radd(d, shallow, shallow);
    let target = div_succ(d, p, 2, n);
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
    let order = rat_eq_rewrite(d, doubled, target, fuse, grown, &|d, t| {
        rle(d, rat, spread, t)
    });
    weaken(d, p, quantity, spread, target, witness, order)
}

/// `Within (seq u j − seq v j) (natDivSucc 2 n)` from `Equiv u v`, given
/// `2/(j+1) ≤ 2/(n+1)`.
fn equiv_between(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    index: ExprId,
    index_order: ExprId,
    n: ExprId,
    hypothesis: ExprId,
) -> ExprId {
    let rat = p.rat;
    let quantity = {
        let a = sample(d, p, u, index);
        let b = sample(d, p, v, index);
        rsub(d, rat, a, b)
    };
    let deep = div_succ(d, p, 2, index);
    let target = div_succ(d, p, 2, n);
    let instance = d.apply(hypothesis, &[index]);
    weaken(d, p, quantity, deep, target, instance, index_order)
}

/// `Within (seq u i − seq v j) (natDivSucc (2+2) n)` from `Equiv u v`.
///
/// The telescope `u_i − v_j = (u_i − u_j) + (u_j − v_j)` — regularity of `u`
/// across the two indices, then the hypothesis at the second one.
fn cross_gap(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    high: ExprId,
    low: ExprId,
    high_le: ExprId,
    low_le: ExprId,
    low_order: ExprId,
    n: ExprId,
    hypothesis: ExprId,
) -> ExprId {
    let rat = p.rat;
    let two_nat = d.num(2);
    let a = sample(d, p, u, high);
    let b = sample(d, p, u, low);
    let c = sample(d, p, v, low);
    let first = rsub(d, rat, a, b);
    let second = rsub(d, rat, b, c);
    let head = regular_between(d, p, u, high, low, high_le, low_le, n);
    let tail = equiv_between(d, p, u, v, low, low_order, n, hypothesis);
    let fused = fuse_at(d, p, first, two_nat, second, two_nat, n, head, tail);
    let summed = radd(d, first, second);
    let target_quantity = rsub(d, rat, a, c);
    let telescope = d.lemma(rat.sub_add_sub, &[a, b, c]);
    let total = NatOps::add(d, two_nat, two_nat);
    let bound = div_succ_at(d, p, total, n);
    rat_eq_rewrite(d, summed, target_quantity, telescope, fused, &|d, t| {
        within(d, p, t, bound)
    })
}

/// `Within (a·b − c·e) (natDivSucc (ka·g₁ + ke·g₂) n)`.
///
/// **The shape every remaining product law reduces to.** `Rat.mul_sub_mul`
/// splits the difference as `a·(b − e) + (a − c)·e`, and each summand pairs a
/// factor bounded by a *canonical magnitude* (`ka`, `ke`) with a factor bounded
/// by a *gap* already read back at `n` (`g₁`, `g₂`). The two gap numerators are
/// separate because `mul_assoc` needs them to be — its outer application has a
/// plain regularity gap on one side and a whole nested product estimate on the
/// other.
#[allow(clippy::too_many_arguments)]
pub(super) fn product_gap(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
    ka: ExprId,
    ke: ExprId,
    g1: ExprId,
    g2: ExprId,
    n: ExprId,
    a_bound: ExprId,
    e_bound: ExprId,
    gap_be: ExprId,
    gap_ac: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let ba = div_succ_at(d, p, ka, zero_nat);
    let be = div_succ_at(d, p, ke, zero_nat);
    let gap_first = div_succ_at(d, p, g1, n);
    let gap_second = div_succ_at(d, p, g2, n);
    let first_quantity = rsub(d, rat, b, e);
    let second_quantity = rsub(d, rat, a, c);

    let ba_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[ka, zero_nat]);
    let gap_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[g2, n]);
    let (al, au) = halves(d, p, a, ba, a_bound);
    let (el, eu) = halves(d, p, e, be, e_bound);
    let (bl, bu) = halves(d, p, first_quantity, gap_first, gap_be);
    let (cl, cu) = halves(d, p, second_quantity, gap_second, gap_ac);

    let head = d.lemma(
        rat.bounds_mul,
        &[a, ba, first_quantity, gap_first, ba_nonneg, al, au, bl, bu],
    );
    let tail = d.lemma(
        rat.bounds_mul,
        &[
            second_quantity,
            gap_second,
            e,
            be,
            gap_nonneg,
            cl,
            cu,
            el,
            eu,
        ],
    );
    let head_term = rmul(d, a, first_quantity);
    let tail_term = rmul(d, second_quantity, e);
    let head_bound = rmul(d, ba, gap_first);
    let tail_bound = rmul(d, gap_second, be);
    let head_numerator = NatOps::mul(d, ka, g1);
    let tail_numerator = NatOps::mul(d, ke, g2);
    let head_target = div_succ_at(d, p, head_numerator, n);
    let tail_target = div_succ_at(d, p, tail_numerator, n);
    let head_fuse = d.lemma(rat.nat_div_succ_mul, &[ka, g1, n]);
    let head_at = rat_eq_rewrite(d, head_bound, head_target, head_fuse, head, &|d, t| {
        within(d, p, head_term, t)
    });
    let tail_at = {
        let swap = d.lemma(rat.mul_comm, &[gap_second, be]);
        let swapped = rmul(d, be, gap_second);
        let fuse = d.lemma(rat.nat_div_succ_mul, &[ke, g2, n]);
        let (_, chain) = rchain(d, tail_bound, &[(swapped, swap), (tail_target, fuse)]);
        rat_eq_rewrite(d, tail_bound, tail_target, chain, tail, &|d, t| {
            within(d, p, tail_term, t)
        })
    };
    let fused = fuse_at(
        d,
        p,
        head_term,
        head_numerator,
        tail_term,
        tail_numerator,
        n,
        head_at,
        tail_at,
    );
    let summed = radd(d, head_term, tail_term);
    let left_product = rmul(d, a, b);
    let right_product = rmul(d, c, e);
    let goal_quantity = rsub(d, rat, left_product, right_product);
    let split = d.lemma(rat.mul_sub_mul, &[a, b, c, e]);
    let back = rsymm(d, goal_quantity, summed, split);
    let total_numerator = NatOps::add(d, head_numerator, tail_numerator);
    let total_bound = div_succ_at(d, p, total_numerator, n);
    rat_eq_rewrite(d, summed, goal_quantity, back, fused, &|d, t| {
        within(d, p, t, total_bound)
    })
}

// --- the canonical bound ----------------------------------------------------

/// `CReal.bound x := Int.natAbs (Rat.num (CReal.seq x 0)) + 1`.
fn declare_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let zero_nat = d.num(0);
    let first = sample(d, p, x, zero_nat);
    let numerator = num(d, first);
    let magnitude = d.const_app(p.rat.int.nat_abs, &[numerator]);
    let body = d.succ(magnitude);
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = d.arrow(carrier, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.bound,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 9),
    })?;

    // mulShift x y := bound x + bound y + 1.
    //
    // Written as a successor so that `c + 1` IS `Kx + Ky` with no ℕ-subtraction
    // anywhere: `(bound x + 1) + (bound y + 1) = succ (succ (bound x + bound
    // y))`, which is `succ (mulShift x y)`.
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let left = bound_of(d, p, x);
    let right = bound_of(d, p, y);
    let total = NatOps::add(d, left, right);
    let body = d.succ(total);
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(carrier, nat);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mul_shift,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 10),
    })
}

/// `bound_within : ∀ x m, Within (seq x m) ((bound x + 1)/1)`.
///
/// `|x_m| ≤ |x_0| + |x_m − x_0| ≤ |num x_0| + (1/(m+1) + 1)` and
/// `1/(m+1) ≤ 1`, so `|x_m| ≤ |num x_0| + 2` — which is
/// `(bound x + 1)/1` because `bound x` is `|num x_0| + 1`. **Every step is a
/// consequence of regularity at the single index `0`**; nothing is extracted
/// and nothing is chosen.
fn declare_bound_within(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let first = sample(d, p, x, zero_nat);
    let numerator = num(d, first);
    let magnitude = d.const_app(p.rat.int.nat_abs, &[numerator]);
    let base = div_succ_at(d, p, magnitude, zero_nat);
    let point = sample(d, p, x, m);
    let target = bound_value(d, p, x);

    let anchor = d.lemma(rat.bounds_num, &[first]);
    let (anchor_low, anchor_high) = halves(d, p, first, base, anchor);
    let gap = rsub(d, rat, point, first);
    let spread = modulus(d, p, m, zero_nat);
    let regular = d.lemma(p.regular, &[x, m, zero_nat]);
    let (gap_low, gap_high) = halves(d, p, gap, spread, regular);
    let combined = d.lemma(
        rat.bounds_add,
        &[
            first,
            base,
            gap,
            spread,
            anchor_low,
            anchor_high,
            gap_low,
            gap_high,
        ],
    );
    let total_bound = radd(d, base, spread);

    // `x_0 + (x_m − x_0) = x_m`.
    let restore = {
        let negated = rneg(d, first);
        let atoms = [first, point, negated];
        let sorted = [point, first, negated];
        let permute = rsum_perm(d, rat, &atoms, &sorted);
        let start = rsum(d, rat, &atoms);
        let sorted_term = rsum(d, rat, &sorted);
        let zero_rat = rzero(d, rat);
        let cancel = d.lemma(rat.add_neg, &[first]);
        let inner = radd(d, first, negated);
        let collapse = rcongr(d, inner, zero_rat, cancel, &|d, t| radd(d, point, t));
        let padded = radd(d, point, zero_rat);
        let trim = d.lemma(rat.add_zero, &[point]);
        let (_, proof) = rchain(
            d,
            start,
            &[(sorted_term, permute), (padded, collapse), (point, trim)],
        );
        proof
    };
    let summed = radd(d, first, gap);
    let at_quantity = rat_eq_rewrite(d, summed, point, restore, combined, &|d, t| {
        within(d, p, t, total_bound)
    });

    // `1/(m+1) + 1/1 ≤ 1/1 + 1/1 = 2/1`, so `|num x_0|/1 + spread ≤
    // (|num x_0| + 2)/1`.
    let unit = div_succ(d, p, 1, zero_nat);
    let deep = div_succ(d, p, 1, m);
    let shallow_le = d.lemma(rat.nat_div_succ_le_one, &[m]);
    let unit_refl = d.lemma(rat.le_refl, &[unit]);
    let widened = d.lemma(
        rat.add_le_add,
        &[deep, unit, unit, unit, shallow_le, unit_refl],
    );
    let doubled = radd(d, unit, unit);
    let two_unit = div_succ(d, p, 2, zero_nat);
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, zero_nat]);
    let spread_le = rat_eq_rewrite(d, doubled, two_unit, fuse, widened, &|d, t| {
        rle(d, rat, spread, t)
    });
    let base_refl = d.lemma(rat.le_refl, &[base]);
    let grown = d.lemma(
        rat.add_le_add,
        &[base, base, spread, two_unit, base_refl, spread_le],
    );
    let padded_bound = radd(d, base, two_unit);
    let fuse_bound = d.lemma(rat.nat_div_succ_add, &[magnitude, two_nat, zero_nat]);
    let order = rat_eq_rewrite(d, padded_bound, target, fuse_bound, grown, &|d, t| {
        rle(d, rat, total_bound, t)
    });
    let body = weaken(d, p, point, total_bound, target, at_quantity, order);

    let value = {
        let over_m = d.lam_fv(m_fv, nat, body);
        d.lam_fv(x_fv, carrier, over_m)
    };
    let ty = {
        let claim = within(d, p, point, target);
        let over_m = d.pi_fv(m_fv, nat, claim);
        d.pi_fv(x_fv, carrier, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bound_within,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the product ------------------------------------------------------------

/// `Eq Rat ((k/1) · (1/(j+1))) (k/(j+1))` — scaling a modulus by a whole
/// number, staying a single `natDivSucc`.
fn scale_modulus(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = p.rat.int.nat;
    let one_nat = d.num(1);
    let fuse = d.lemma(rat.nat_div_succ_mul, &[k, one_nat, j]);
    let scaled_numerator = NatOps::mul(d, k, one_nat);
    let from = div_succ_at(d, p, scaled_numerator, j);
    let trim = d.lemma(nat.mul_one, &[k]);
    let tidy = nat_eq_to_rat(d, scaled_numerator, k, trim, &|d, t| {
        div_succ_at(d, p, t, j)
    });
    let target = div_succ_at(d, p, k, j);
    let start = {
        let zero_nat = d.num(0);
        let left = div_succ_at(d, p, k, zero_nat);
        let right = div_succ(d, p, 1, j);
        rmul(d, left, right)
    };
    let (_, proof) = rchain(d, start, &[(from, fuse), (target, tidy)]);
    proof
}

/// `Eq Nat ((bound x + 1) + (bound y + 1)) (mulShift x y + 1)`.
fn magnitudes_sum(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let nat = p.rat.int.nat;
    let bx = bound_of(d, p, x);
    let by = bound_of(d, p, y);
    let kx = d.succ(bx);
    let ky = d.succ(by);
    let start = NatOps::add(d, kx, ky);
    let first = d.lemma(nat.add_succ, &[kx, by]);
    let inner = NatOps::add(d, kx, by);
    let stepped = d.succ(inner);
    let second = d.lemma(nat.succ_add, &[bx, by]);
    let plain = NatOps::add(d, bx, by);
    let target = {
        let inner_succ = d.succ(plain);
        d.succ(inner_succ)
    };
    let stepped_plain = d.succ(plain);
    let lifted = NatOps::congr(d, inner, stepped_plain, second, &|d, t| d.succ(t));
    let (_, proof) = NatOps::chain(d, start, &[(stepped, first), (target, lifted)]);
    proof
}

/// `CReal.mul`, with Bishop's product index.
fn declare_mul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let shift = mul_shift(d, p, x, y);

    let representative = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let index = mul_index(d, shift, n);
        let left = sample(d, p, x, index);
        let right = sample(d, p, y, index);
        let body = rmul(d, left, right);
        d.lam_fv(n_fv, nat, body)
    };

    let regularity = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let high = mul_index(d, shift, m);
        let low = mul_index(d, shift, n);
        let a = sample(d, p, x, high);
        let b = sample(d, p, y, high);
        let c = sample(d, p, x, low);
        let e = sample(d, p, y, low);

        let zero_nat = d.num(0);
        let one_nat = d.num(1);
        let kx = magnitude_of(d, p, x);
        let ky = magnitude_of(d, p, y);
        let bx = bound_value(d, p, x);
        let by = bound_value(d, p, y);
        let spread = modulus(d, p, high, low);
        let spread_nonneg = {
            let left = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, high]);
            let right = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, low]);
            let left_atom = div_succ(d, p, 1, high);
            let right_atom = div_succ(d, p, 1, low);
            d.lemma(rat.add_nonneg, &[left_atom, right_atom, left, right])
        };
        let bx_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[kx, zero_nat]);

        let x_bound = d.lemma(p.bound_within, &[x, high]);
        let (xb_low, xb_high) = halves(d, p, a, bx, x_bound);
        let y_bound = d.lemma(p.bound_within, &[y, low]);
        let (yb_low, yb_high) = halves(d, p, e, by, y_bound);
        let y_gap = rsub(d, rat, b, e);
        let y_regular = d.lemma(p.regular, &[y, high, low]);
        let (yg_low, yg_high) = halves(d, p, y_gap, spread, y_regular);
        let x_gap = rsub(d, rat, a, c);
        let x_regular = d.lemma(p.regular, &[x, high, low]);
        let (xg_low, xg_high) = halves(d, p, x_gap, spread, x_regular);

        let head = d.lemma(
            rat.bounds_mul,
            &[
                a, bx, y_gap, spread, bx_nonneg, xb_low, xb_high, yg_low, yg_high,
            ],
        );
        let tail = d.lemma(
            rat.bounds_mul,
            &[
                x_gap,
                spread,
                e,
                by,
                spread_nonneg,
                xg_low,
                xg_high,
                yb_low,
                yb_high,
            ],
        );
        let head_term = rmul(d, a, y_gap);
        let tail_term = rmul(d, x_gap, e);
        let head_bound = rmul(d, bx, spread);
        let tail_bound = rmul(d, spread, by);
        let (head_low, head_high) = halves(d, p, head_term, head_bound, head);
        let (tail_low, tail_high) = halves(d, p, tail_term, tail_bound, tail);
        let combined = d.lemma(
            rat.bounds_add,
            &[
                head_term, head_bound, tail_term, tail_bound, head_low, head_high, tail_low,
                tail_high,
            ],
        );
        let summed_quantity = radd(d, head_term, tail_term);
        let summed_bound = radd(d, head_bound, tail_bound);

        // The quantity: `a·b − c·e = a·(b − e) + (a − c)·e`.
        let left_product = rmul(d, a, b);
        let right_product = rmul(d, c, e);
        let goal_quantity = rsub(d, rat, left_product, right_product);
        let split = d.lemma(rat.mul_sub_mul, &[a, b, c, e]);
        let back = rsymm(d, goal_quantity, summed_quantity, split);
        let at_quantity = rat_eq_rewrite(
            d,
            summed_quantity,
            goal_quantity,
            back,
            combined,
            &|d, t| within(d, p, t, summed_bound),
        );

        // The bound. `Kx/1 · spread` opens by `left_distrib` into two scaled
        // moduli, and `natDivSucc_mul` fuses each back into one `natDivSucc`.
        let kx_high = div_succ_at(d, p, kx, high);
        let kx_low = div_succ_at(d, p, kx, low);
        let ky_high = div_succ_at(d, p, ky, high);
        let ky_low = div_succ_at(d, p, ky, low);
        let one_high = div_succ(d, p, 1, high);
        let one_low = div_succ(d, p, 1, low);

        let open_head = {
            let distrib = d.lemma(rat.left_distrib, &[bx, one_high, one_low]);
            let scaled_high = rmul(d, bx, one_high);
            let scaled_low = rmul(d, bx, one_low);
            let opened = radd(d, scaled_high, scaled_low);
            let fuse_high = scale_modulus(d, p, kx, high);
            let after_high = rcongr(d, scaled_high, kx_high, fuse_high, &|d, t| {
                radd(d, t, scaled_low)
            });
            let staged = radd(d, kx_high, scaled_low);
            let fuse_low = scale_modulus(d, p, kx, low);
            let after_low = rcongr(d, scaled_low, kx_low, fuse_low, &|d, t| radd(d, kx_high, t));
            let target = radd(d, kx_high, kx_low);
            let (_, proof) = rchain(
                d,
                head_bound,
                &[(opened, distrib), (staged, after_high), (target, after_low)],
            );
            proof
        };
        let head_pair = radd(d, kx_high, kx_low);
        let open_tail = {
            let swap = d.lemma(rat.mul_comm, &[spread, by]);
            let swapped = rmul(d, by, spread);
            let distrib = d.lemma(rat.left_distrib, &[by, one_high, one_low]);
            let scaled_high = rmul(d, by, one_high);
            let scaled_low = rmul(d, by, one_low);
            let opened = radd(d, scaled_high, scaled_low);
            let fuse_high = scale_modulus(d, p, ky, high);
            let after_high = rcongr(d, scaled_high, ky_high, fuse_high, &|d, t| {
                radd(d, t, scaled_low)
            });
            let staged = radd(d, ky_high, scaled_low);
            let fuse_low = scale_modulus(d, p, ky, low);
            let after_low = rcongr(d, scaled_low, ky_low, fuse_low, &|d, t| radd(d, ky_high, t));
            let target = radd(d, ky_high, ky_low);
            let (_, proof) = rchain(
                d,
                tail_bound,
                &[
                    (swapped, swap),
                    (opened, distrib),
                    (staged, after_high),
                    (target, after_low),
                ],
            );
            proof
        };
        let tail_pair = radd(d, ky_high, ky_low);

        let after_head = rcongr(d, head_bound, head_pair, open_head, &|d, t| {
            radd(d, t, tail_bound)
        });
        let staged_bound = radd(d, head_pair, tail_bound);
        let after_tail = rcongr(d, tail_bound, tail_pair, open_tail, &|d, t| {
            radd(d, head_pair, t)
        });
        let opened_bound = radd(d, head_pair, tail_pair);

        let flat_atoms = [kx_high, kx_low, ky_high, ky_low];
        let sorted_atoms = [kx_high, ky_high, kx_low, ky_low];
        let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
        let flat = rsum(d, rat, &flat_atoms);
        let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
        let sorted = rsum(d, rat, &sorted_atoms);
        let paired = {
            let forward = rsum_append(d, rat, &sorted_atoms[..2], &sorted_atoms[2..]);
            let left = radd(d, kx_high, ky_high);
            let right = radd(d, kx_low, ky_low);
            let target = radd(d, left, right);
            rsymm(d, target, sorted, forward)
        };
        let high_pair = radd(d, kx_high, ky_high);
        let low_pair = radd(d, kx_low, ky_low);
        let pair_target = radd(d, high_pair, low_pair);

        let total_numerator = NatOps::add(d, kx, ky);
        let fused_high = div_succ_at(d, p, total_numerator, high);
        let fused_low = div_succ_at(d, p, total_numerator, low);
        let fuse_high = d.lemma(rat.nat_div_succ_add, &[kx, ky, high]);
        let after_fuse_high = rcongr(d, high_pair, fused_high, fuse_high, &|d, t| {
            radd(d, t, low_pair)
        });
        let staged_fuse = radd(d, fused_high, low_pair);
        let fuse_low = d.lemma(rat.nat_div_succ_add, &[kx, ky, low]);
        let after_fuse_low = rcongr(d, low_pair, fused_low, fuse_low, &|d, t| {
            radd(d, fused_high, t)
        });
        let fused = radd(d, fused_high, fused_low);

        // `Kx + Ky = c + 1`, so both fused moduli are `(c+1)/((c+1)·i + c + 1)`
        // and `natDivSucc_scale` reads each as the regularity bound outright.
        let successor = d.succ(shift);
        let sum_eq = magnitudes_sum(d, p, x, y);
        let scaled_high = div_succ_at(d, p, successor, high);
        let scaled_low = div_succ_at(d, p, successor, low);
        let align_high = nat_eq_to_rat(d, total_numerator, successor, sum_eq, &|d, t| {
            div_succ_at(d, p, t, high)
        });
        let after_align_high = rcongr(d, fused_high, scaled_high, align_high, &|d, t| {
            radd(d, t, fused_low)
        });
        let staged_align = radd(d, scaled_high, fused_low);
        let align_low = nat_eq_to_rat(d, total_numerator, successor, sum_eq, &|d, t| {
            div_succ_at(d, p, t, low)
        });
        let after_align_low = rcongr(d, fused_low, scaled_low, align_low, &|d, t| {
            radd(d, scaled_high, t)
        });
        let aligned = radd(d, scaled_high, scaled_low);

        let one_m = div_succ(d, p, 1, m);
        let one_n = div_succ(d, p, 1, n);
        let scale_high = d.lemma(rat.nat_div_succ_scale, &[shift, m]);
        let after_scale_high = rcongr(d, scaled_high, one_m, scale_high, &|d, t| {
            radd(d, t, scaled_low)
        });
        let staged_scale = radd(d, one_m, scaled_low);
        let scale_low = d.lemma(rat.nat_div_succ_scale, &[shift, n]);
        let after_scale_low = rcongr(d, scaled_low, one_n, scale_low, &|d, t| radd(d, one_m, t));
        let goal_bound = modulus(d, p, m, n);

        let (_, bound_chain) = rchain(
            d,
            summed_bound,
            &[
                (staged_bound, after_head),
                (opened_bound, after_tail),
                (flat, flatten),
                (sorted, permute),
                (pair_target, paired),
                (staged_fuse, after_fuse_high),
                (fused, after_fuse_low),
                (staged_align, after_align_high),
                (aligned, after_align_low),
                (staged_scale, after_scale_high),
                (goal_bound, after_scale_low),
            ],
        );
        let moved = rat_eq_rewrite(
            d,
            summed_bound,
            goal_bound,
            bound_chain,
            at_quantity,
            &|d, t| within(d, p, goal_quantity, t),
        );
        let over_n = d.lam_fv(n_fv, nat, moved);
        d.lam_fv(m_fv, nat, over_n)
    };

    let constructor = d.kernel().const_(p.mk, vec![]);
    let body = d.apply(constructor, &[representative, regularity]);
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(carrier, carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mul,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 11),
    })
}

// --- the closing lemma -------------------------------------------------------

/// `equiv_of_bounded : ∀ x y (K : Nat), (∀ n, Within (x_n − y_n) (K/(n+1))) →
/// Equiv x y`.
///
/// **`Equiv` only needs the difference to be `O(1/n)` — the constant is free.**
/// This is what makes the product laws whose two sides sample at *different*
/// indices provable at all: the exact `2/(n+1)` bookkeeping `CReal.mul`'s own
/// regularity achieves is not available across two different shifts, and it
/// does not have to be.
///
/// It is `Equiv.trans`'s argument with one term deleted. Compare at an
/// arbitrary third index `j`:
///
/// ```text
/// |x_n − y_n| ≤ |x_n − x_j| + |x_j − y_j| + |y_j − y_n|
///             ≤ (1/(n+1) + 1/(j+1)) + K/(j+1) + (1/(j+1) + 1/(n+1))
///              = 2/(n+1) + (K+2)/(j+1)
/// ```
///
/// and the `(K+2)/(j+1)` is discharged by the **Archimedean property of ℚ**,
/// whose numerator is a `Nat` *parameter* — so a symbolic constant built out of
/// the two factors' `CReal.bound`s is as acceptable as a literal. That is the
/// whole reason the crude estimates below are allowed to be crude.
fn declare_equiv_of_bounded(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let hypothesis = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let a = sample(d, p, x, n);
        let b = sample(d, p, y, n);
        let difference = rsub(d, rat, a, b);
        let bound = div_succ_at(d, p, k, n);
        let claim = within(d, p, difference, bound);
        d.pi_fv(n_fv, nat, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let head = sample(d, p, x, n);
    let tail = sample(d, p, y, n);
    let target = rsub(d, rat, head, tail);
    let goal_bound = div_succ(d, p, 2, n);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let inner_numerator = NatOps::add(d, one_nat, k);
    let slack_numerator = NatOps::add(d, one_nat, inner_numerator);

    // The estimate at an arbitrary index `j`, as a function of `j`.
    let estimate = |d: &mut IntDev<'_>, j: ExprId| -> (ExprId, ExprId) {
        let xj = sample(d, p, x, j);
        let yj = sample(d, p, y, j);
        let u1 = rsub(d, rat, head, xj);
        let u2 = rsub(d, rat, xj, yj);
        let u3 = rsub(d, rat, yj, tail);
        let b1 = modulus(d, p, n, j);
        let b2 = div_succ_at(d, p, k, j);
        let b3 = modulus(d, p, j, n);

        let w1 = d.lemma(p.regular, &[x, n, j]);
        let w2 = d.apply(h, &[j]);
        let w3 = d.lemma(p.regular, &[y, j, n]);
        let (l1, r1) = halves(d, p, u1, b1, w1);
        let (l2, r2) = halves(d, p, u2, b2, w2);
        let (l3, r3) = halves(d, p, u3, b3, w3);

        let w23 = d.lemma(rat.bounds_add, &[u2, b2, u3, b3, l2, r2, l3, r3]);
        let q23 = radd(d, u2, u3);
        let c23 = radd(d, b2, b3);
        let (l23, r23) = halves(d, p, q23, c23, w23);
        let w123 = d.lemma(rat.bounds_add, &[u1, b1, q23, c23, l1, r1, l23, r23]);
        let q123 = radd(d, u1, q23);
        let c123 = radd(d, b1, c23);

        // The quantity telescopes: `(a − x_j) + ((x_j − y_j) + (y_j − b))`.
        let mid = rsub(d, rat, xj, tail);
        let inner_step = d.lemma(rat.sub_add_sub, &[xj, yj, tail]);
        let outer_step = d.lemma(rat.sub_add_sub, &[head, xj, tail]);
        let staged = radd(d, u1, mid);
        let first = rcongr(d, q23, mid, inner_step, &|d, t| radd(d, u1, t));
        let (_, quantity) = rchain(d, q123, &[(staged, first), (target, outer_step)]);

        // The bound fuses: `(A+B) + (C + (B+A)) = 2/(n+1) + (K+2)/(j+1)`.
        let a_atom = div_succ(d, p, 1, n);
        let b_atom = div_succ(d, p, 1, j);
        let c_atom = div_succ_at(d, p, k, j);
        let flat_atoms = [a_atom, b_atom, c_atom, b_atom, a_atom];
        let sorted_atoms = [a_atom, a_atom, b_atom, b_atom, c_atom];
        let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
        let flat = rsum(d, rat, &flat_atoms);
        let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
        let sorted = rsum(d, rat, &sorted_atoms);
        let head_pair = radd(d, a_atom, a_atom);
        let tail_triple = rsum(d, rat, &sorted_atoms[2..]);
        let paired = {
            let forward = rsum_append(d, rat, &sorted_atoms[..2], &sorted_atoms[2..]);
            let target_term = radd(d, head_pair, tail_triple);
            rsymm(d, target_term, sorted, forward)
        };
        let pair_target = radd(d, head_pair, tail_triple);
        let fuse_head = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let after_head = rcongr(d, head_pair, goal_bound, fuse_head, &|d, t| {
            radd(d, t, tail_triple)
        });
        let staged_head = radd(d, goal_bound, tail_triple);
        let inner_pair = radd(d, b_atom, c_atom);
        let inner_fused = div_succ_at(d, p, inner_numerator, j);
        let fuse_inner = d.lemma(rat.nat_div_succ_add, &[one_nat, k, j]);
        let after_inner = rcongr(d, inner_pair, inner_fused, fuse_inner, &|d, t| {
            let outer = radd(d, b_atom, t);
            radd(d, goal_bound, outer)
        });
        let staged_inner = {
            let outer = radd(d, b_atom, inner_fused);
            radd(d, goal_bound, outer)
        };
        let outer_pair = radd(d, b_atom, inner_fused);
        let slack = div_succ_at(d, p, slack_numerator, j);
        let fuse_outer = d.lemma(rat.nat_div_succ_add, &[one_nat, inner_numerator, j]);
        let after_outer = rcongr(d, outer_pair, slack, fuse_outer, &|d, t| {
            radd(d, goal_bound, t)
        });
        let final_bound = radd(d, goal_bound, slack);
        let (_, bound_chain) = rchain(
            d,
            c123,
            &[
                (flat, flatten),
                (sorted, permute),
                (pair_target, paired),
                (staged_head, after_head),
                (staged_inner, after_inner),
                (final_bound, after_outer),
            ],
        );

        let at_quantity = rat_eq_rewrite(d, q123, target, quantity, w123, &|d, t| {
            within(d, p, t, c123)
        });
        let moved = rat_eq_rewrite(d, c123, final_bound, bound_chain, at_quantity, &|d, t| {
            within(d, p, target, t)
        });
        (final_bound, moved)
    };

    // Upper half, then the same estimate negated for the lower half — exactly
    // `Equiv.trans`'s shape, and for the same reason.
    let upper_hypothesis = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (bound, proof) = estimate(d, j);
        let (_, upper) = halves(d, p, target, bound, proof);
        d.lam_fv(j_fv, nat, upper)
    };
    let upper = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[target, goal_bound, slack_numerator, upper_hypothesis],
    );
    let negated_target = rneg(d, target);
    let lower_hypothesis = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (bound, proof) = estimate(d, j);
        let (low, high) = halves(d, p, target, bound, proof);
        let flipped = d.lemma(rat.bounds_neg, &[target, bound, low, high]);
        let negated_bound = rneg(d, bound);
        let inner_lower = rle(d, rat, negated_bound, negated_target);
        let inner_upper = rle(d, rat, negated_target, bound);
        let body = d.and_right(inner_lower, inner_upper, flipped);
        d.lam_fv(j_fv, nat, body)
    };
    let lower_raw = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[
            negated_target,
            goal_bound,
            slack_numerator,
            lower_hypothesis,
        ],
    );
    let lower_negated = d.lemma(rat.neg_le_neg, &[negated_target, goal_bound, lower_raw]);
    let twice = rneg(d, negated_target);
    let cancel = d.lemma(rat.neg_neg, &[target]);
    let negated_goal = rneg(d, goal_bound);
    let lower = rat_eq_rewrite(d, twice, target, cancel, lower_negated, &|d, t| {
        rle(d, rat, negated_goal, t)
    });
    let lower_ty = rle(d, rat, negated_goal, target);
    let upper_ty = rle(d, rat, target, goal_bound);
    let pair = {
        let intro = p.rat.int.logic.and_intro;
        d.const_app(intro, &[lower_ty, upper_ty, lower, upper])
    };
    let _ = two_nat;

    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_y = d.lam_fv(y_fv, carrier, with_k);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, x, y);
        let after_h = d.arrow(hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, after_h);
        let with_y = d.pi_fv(y_fv, carrier, with_k);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_of_bounded,
        uparams: vec![],
        ty,
        value,
    })
}

/// `mul_congr : ∀ x x' y y', Equiv x x' → Equiv y y' →
/// Equiv (mul x y) (mul x' y')`.
///
/// The **fifth congruence obligation**, and the one ADR-0512 calls the setoid's
/// real tax. It is not one of the 22, and it is a prerequisite for phase R4.
///
/// It is the first law whose two sides sample at indices derived from
/// *different* bounds: `mul x y` samples at `(c+1)·n + c` and `mul x' y'` at
/// `(c'+1)·n + c'`, with no relation between `c` and `c'`. The exact estimate
/// `CReal.mul`'s own regularity achieves is therefore unavailable, and the
/// naive bound is `C/(n+1)` for a `C > 2` — which is exactly what
/// [`declare_equiv_of_bounded`] is for. Split the difference with
/// `Rat.mul_sub_mul`, bound one factor of each summand by its canonical
/// magnitude and the other by regularity-plus-hypothesis read back at `n`, and
/// the constant comes out as `Kx·4 + Ky'·4`.
fn declare_mul_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let x2_fv = d.fresh_fvar();
    let x2 = d.kernel().fvar(x2_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let y2_fv = d.fresh_fvar();
    let y2 = d.kernel().fvar(y2_fv);
    let first_ty = equiv(d, p, x, x2);
    let second_ty = equiv(d, p, y, y2);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let left = cmul(d, p, x, y);
    let right = cmul(d, p, x2, y2);
    let two_nat = d.num(2);
    let gap_numerator = NatOps::add(d, two_nat, two_nat);
    let kx = magnitude_of(d, p, x);
    let ky2 = magnitude_of(d, p, y2);
    let head_numerator = NatOps::mul(d, kx, gap_numerator);
    let tail_numerator = NatOps::mul(d, ky2, gap_numerator);
    let total_numerator = NatOps::add(d, head_numerator, tail_numerator);

    let at_index = {
        let one_nat = d.num(1);
        let shift = mul_shift(d, p, x, y);
        let mirrored = mul_shift(d, p, x2, y2);
        let high = mul_index(d, shift, n);
        let low = mul_index(d, mirrored, n);
        let high_le = index_le(d, p, one_nat, shift, n);
        let low_le = index_le(d, p, one_nat, mirrored, n);
        let low_order = index_le(d, p, two_nat, mirrored, n);
        let a = sample(d, p, x, high);
        let b = sample(d, p, y, high);
        let a2 = sample(d, p, x2, low);
        let b2 = sample(d, p, y2, low);
        let _ = (a2, b2);

        let x_gap_proof = cross_gap(d, p, x, x2, high, low, high_le, low_le, low_order, n, h1);
        let high_le = index_le(d, p, one_nat, shift, n);
        let low_le = index_le(d, p, one_nat, mirrored, n);
        let low_order = index_le(d, p, two_nat, mirrored, n);
        let y_gap_proof = cross_gap(d, p, y, y2, high, low, high_le, low_le, low_order, n, h2);
        let bx_witness = d.lemma(p.bound_within, &[x, high]);
        let by2_witness = d.lemma(p.bound_within, &[y2, low]);
        let a2 = sample(d, p, x2, low);
        let b2 = sample(d, p, y2, low);
        product_gap(
            d,
            p,
            a,
            b,
            a2,
            b2,
            kx,
            ky2,
            gap_numerator,
            gap_numerator,
            n,
            bx_witness,
            by2_witness,
            y_gap_proof,
            x_gap_proof,
        )
    };

    let witness = d.lam_fv(n_fv, nat, at_index);
    let body = d.lemma(p.equiv_of_bounded, &[left, right, total_numerator, witness]);
    let value = {
        let with_second = d.lam_fv(h2_fv, second_ty, body);
        let with_first = d.lam_fv(h1_fv, first_ty, with_second);
        let with_y2 = d.lam_fv(y2_fv, carrier, with_first);
        let with_y = d.lam_fv(y_fv, carrier, with_y2);
        let with_x2 = d.lam_fv(x2_fv, carrier, with_y);
        d.lam_fv(x_fv, carrier, with_x2)
    };
    let ty = {
        let conclusion = equiv(d, p, left, right);
        let after_second = d.arrow(second_ty, conclusion);
        let after_first = d.arrow(first_ty, after_second);
        let with_y2 = d.pi_fv(y2_fv, carrier, after_first);
        let with_y = d.pi_fv(y_fv, carrier, with_y2);
        let with_x2 = d.pi_fv(x2_fv, carrier, with_y);
        d.pi_fv(x_fv, carrier, with_x2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `left_distrib : ∀ x y z, Equiv (mul x (add y z)) (add (mul x y) (mul x z))`
/// — one of the 22, in `Equiv` form.
///
/// Every index in sight is different: the left side samples `x` at
/// `(c₁+1)·n + c₁` and `y`, `z` one additive shift deeper still, while the right
/// side samples `x` twice more, at two *further* product indices derived from
/// `mulShift x y` and `mulShift x z`. Nothing agrees anywhere, and the shifts
/// are not equal as naturals.
///
/// What makes it tractable is that all four indices are the **same shape**:
/// `Rat.nat_index_compose` says a product index of a product index is a product
/// index, and Bishop's additive shift `2n+1` *is* the `c = 1` case — so
/// [`composed_index_le`] reads every one of them back at `n` and the whole
/// estimate is `O(1/n)` with a symbolic constant, which is all
/// [`declare_equiv_of_bounded`] asks for.
fn declare_left_distrib(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sum = cadd(d, p, y, z);
    let left = cmul(d, p, x, sum);
    let right = {
        let first = cmul(d, p, x, y);
        let second = cmul(d, p, x, z);
        cadd(d, p, first, second)
    };

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let kx = magnitude_of(d, p, x);
    let ky = magnitude_of(d, p, y);
    let kz = magnitude_of(d, p, z);
    let head_numerator = {
        let a = NatOps::mul(d, kx, two_nat);
        let b = NatOps::mul(d, ky, two_nat);
        NatOps::add(d, a, b)
    };
    let tail_numerator = {
        let a = NatOps::mul(d, kx, two_nat);
        let b = NatOps::mul(d, kz, two_nat);
        NatOps::add(d, a, b)
    };
    let total_numerator = NatOps::add(d, head_numerator, tail_numerator);

    let at_index = {
        let outer = mul_shift(d, p, x, sum);
        let left_shift = mul_shift(d, p, x, y);
        let right_shift = mul_shift(d, p, x, z);
        let deep = mul_index(d, outer, n);
        let shifted = mul_index(d, one_nat, n);
        let inner = mul_index(d, one_nat, deep);
        let left_index = mul_index(d, left_shift, shifted);
        let right_index = mul_index(d, right_shift, shifted);

        let xa = sample(d, p, x, deep);
        let yt = sample(d, p, y, inner);
        let zt = sample(d, p, z, inner);
        let xp = sample(d, p, x, left_index);
        let yp = sample(d, p, y, left_index);
        let xq = sample(d, p, x, right_index);
        let zq = sample(d, p, z, right_index);

        // The first summand, `x_A·y_T − x_P·y_P`.
        let head = {
            let gap_y = {
                let inner_le = composed_index_le(d, p, one_nat, one_nat, outer, n);
                let left_le = composed_index_le(d, p, one_nat, left_shift, one_nat, n);
                regular_between(d, p, y, inner, left_index, inner_le, left_le, n)
            };
            let gap_x = {
                let deep_le = index_le(d, p, one_nat, outer, n);
                let left_le = composed_index_le(d, p, one_nat, left_shift, one_nat, n);
                regular_between(d, p, x, deep, left_index, deep_le, left_le, n)
            };
            let x_bound = d.lemma(p.bound_within, &[x, deep]);
            let y_bound = d.lemma(p.bound_within, &[y, left_index]);
            product_gap(
                d, p, xa, yt, xp, yp, kx, ky, two_nat, two_nat, n, x_bound, y_bound, gap_y, gap_x,
            )
        };
        // The second summand, `x_A·z_T − x_Q·z_Q`.
        let tail = {
            let gap_z = {
                let inner_le = composed_index_le(d, p, one_nat, one_nat, outer, n);
                let right_le = composed_index_le(d, p, one_nat, right_shift, one_nat, n);
                regular_between(d, p, z, inner, right_index, inner_le, right_le, n)
            };
            let gap_x = {
                let deep_le = index_le(d, p, one_nat, outer, n);
                let right_le = composed_index_le(d, p, one_nat, right_shift, one_nat, n);
                regular_between(d, p, x, deep, right_index, deep_le, right_le, n)
            };
            let x_bound = d.lemma(p.bound_within, &[x, deep]);
            let z_bound = d.lemma(p.bound_within, &[z, right_index]);
            product_gap(
                d, p, xa, zt, xq, zq, kx, kz, two_nat, two_nat, n, x_bound, z_bound, gap_z, gap_x,
            )
        };
        let head_term = {
            let a = rmul(d, xa, yt);
            let b = rmul(d, xp, yp);
            rsub(d, rat, a, b)
        };
        let tail_term = {
            let a = rmul(d, xa, zt);
            let b = rmul(d, xq, zq);
            rsub(d, rat, a, b)
        };
        let fused = fuse_at(
            d,
            p,
            head_term,
            head_numerator,
            tail_term,
            tail_numerator,
            n,
            head,
            tail,
        );
        let summed = radd(d, head_term, tail_term);

        // The quantity: `(x_A·y_T + x_A·z_T) − (x_P·y_P + x_Q·z_Q)`, and the
        // left half is `x_A·(y_T + z_T)` — the `ℚ` distributive law, once.
        let first_product = rmul(d, xa, yt);
        let second_product = rmul(d, xa, zt);
        let third_product = rmul(d, xp, yp);
        let fourth_product = rmul(d, xq, zq);
        let opened_left = radd(d, first_product, second_product);
        let right_sum = radd(d, third_product, fourth_product);
        let split = d.lemma(
            rat.sub_add_add,
            &[first_product, second_product, third_product, fourth_product],
        );
        let opened_difference = rsub(d, rat, opened_left, right_sum);
        let back = rsymm(d, opened_difference, summed, split);
        let inner_sum = radd(d, yt, zt);
        let folded = rmul(d, xa, inner_sum);
        let distrib = d.lemma(rat.left_distrib, &[xa, yt, zt]);
        let fold = rsymm(d, folded, opened_left, distrib);
        let goal_quantity = rsub(d, rat, folded, right_sum);
        let refold = rcongr(d, opened_left, folded, fold, &|d, t| {
            rsub(d, rat, t, right_sum)
        });
        let (_, quantity) = rchain(
            d,
            summed,
            &[(opened_difference, back), (goal_quantity, refold)],
        );
        let total_bound = div_succ_at(d, p, total_numerator, n);
        rat_eq_rewrite(d, summed, goal_quantity, quantity, fused, &|d, t| {
            within(d, p, t, total_bound)
        })
    };

    let witness = d.lam_fv(n_fv, nat, at_index);
    let body = d.lemma(p.equiv_of_bounded, &[left, right, total_numerator, witness]);
    let value = {
        let with_z = d.lam_fv(z_fv, carrier, body);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, left, right);
        let with_z = d.pi_fv(z_fv, carrier, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.left_distrib,
        uparams: vec![],
        ty,
        value,
    })
}

/// Chain `Equiv start …` through `(next, step)` pairs, the way
/// [`rchain`] chains `Eq`.
///
/// `pub(super)`: `sqrt.rs`'s `declare_sqrt_mul` reuses this for its own
/// ring-rearrangement chain (`(sqrt x·sqrt y)² ~ (sqrt x)²·(sqrt y)²`).
pub(super) fn equiv_chain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    (current, proof)
}

/// `mul_assoc : ∀ x y z, Equiv (mul (mul x y) z) (mul x (mul y z))` — one of
/// the 22, in `Equiv` form.
///
/// The last of the eight, and the one with a **nested** sampling index on each
/// side: the left samples `x` and `y` at a product index *of* a product index,
/// the right does the same to `y` and `z`. `Rat.nat_index_compose` is what
/// makes that shape reducible at all.
///
/// It is also the only law that needs [`product_gap`] **twice**, at two levels:
/// once on `x_P·y_P − x_B·y_Q`, and again on the outside with that whole
/// estimate as one of its two gaps — which is why `product_gap` takes two
/// separate gap numerators rather than one.
fn declare_mul_assoc(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let inner_left = cmul(d, p, x, y);
    let inner_right = cmul(d, p, y, z);
    let left = cmul(d, p, inner_left, z);
    let right = cmul(d, p, x, inner_right);

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let zero_nat = d.num(0);
    let kx = magnitude_of(d, p, x);
    let ky = magnitude_of(d, p, y);
    let kz = magnitude_of(d, p, z);
    let pair_numerator = NatOps::mul(d, kx, ky);
    let inner_numerator = {
        let a = NatOps::mul(d, kx, two_nat);
        let b = NatOps::mul(d, ky, two_nat);
        NatOps::add(d, a, b)
    };
    let total_numerator = {
        let head = NatOps::mul(d, pair_numerator, two_nat);
        let tail = NatOps::mul(d, kz, inner_numerator);
        NatOps::add(d, head, tail)
    };

    let at_index = {
        let outer_left = mul_shift(d, p, inner_left, z);
        let deep_left = mul_shift(d, p, x, y);
        let outer_right = mul_shift(d, p, x, inner_right);
        let deep_right = mul_shift(d, p, y, z);
        let shallow_left = mul_index(d, outer_left, n);
        let pair_index = mul_index(d, deep_left, shallow_left);
        let shallow_right = mul_index(d, outer_right, n);
        let mirror_index = mul_index(d, deep_right, shallow_right);

        let xp = sample(d, p, x, pair_index);
        let yp = sample(d, p, y, pair_index);
        let za = sample(d, p, z, shallow_left);
        let xb = sample(d, p, x, shallow_right);
        let yq = sample(d, p, y, mirror_index);
        let zq = sample(d, p, z, mirror_index);

        // `|x_P·y_P| ≤ Kx·Ky`, the canonical magnitude of a product.
        let bx = bound_value(d, p, x);
        let by = bound_value(d, p, y);
        let pair_bound = {
            let x_witness = d.lemma(p.bound_within, &[x, pair_index]);
            let y_witness = d.lemma(p.bound_within, &[y, pair_index]);
            let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[kx, zero_nat]);
            let (xl, xu) = halves(d, p, xp, bx, x_witness);
            let (yl, yu) = halves(d, p, yp, by, y_witness);
            let product = d.lemma(rat.bounds_mul, &[xp, bx, yp, by, nonneg, xl, xu, yl, yu]);
            let raw = rmul(d, bx, by);
            let target = div_succ_at(d, p, pair_numerator, zero_nat);
            let fuse = d.lemma(rat.nat_div_succ_mul, &[kx, ky, zero_nat]);
            let quantity = rmul(d, xp, yp);
            rat_eq_rewrite(d, raw, target, fuse, product, &|d, t| {
                within(d, p, quantity, t)
            })
        };

        // The inner estimate, `x_P·y_P − x_B·y_Q`.
        let inner_gap = {
            let gap_y = {
                let pair_le = composed_index_le(d, p, one_nat, deep_left, outer_left, n);
                let mirror_le = composed_index_le(d, p, one_nat, deep_right, outer_right, n);
                regular_between(d, p, y, pair_index, mirror_index, pair_le, mirror_le, n)
            };
            let gap_x = {
                let pair_le = composed_index_le(d, p, one_nat, deep_left, outer_left, n);
                let shallow_le = index_le(d, p, one_nat, outer_right, n);
                regular_between(d, p, x, pair_index, shallow_right, pair_le, shallow_le, n)
            };
            let x_bound = d.lemma(p.bound_within, &[x, pair_index]);
            let y_bound = d.lemma(p.bound_within, &[y, mirror_index]);
            product_gap(
                d, p, xp, yp, xb, yq, kx, ky, two_nat, two_nat, n, x_bound, y_bound, gap_y, gap_x,
            )
        };

        // The outer estimate, with the inner one as its second gap.
        let gap_z = {
            let shallow_le = index_le(d, p, one_nat, outer_left, n);
            let mirror_le = composed_index_le(d, p, one_nat, deep_right, outer_right, n);
            regular_between(
                d,
                p,
                z,
                shallow_left,
                mirror_index,
                shallow_le,
                mirror_le,
                n,
            )
        };
        let z_bound = d.lemma(p.bound_within, &[z, mirror_index]);
        let pair_term = rmul(d, xp, yp);
        let mirror_pair = rmul(d, xb, yq);
        let estimate = product_gap(
            d,
            p,
            pair_term,
            za,
            mirror_pair,
            zq,
            pair_numerator,
            kz,
            two_nat,
            inner_numerator,
            n,
            pair_bound,
            z_bound,
            gap_z,
            inner_gap,
        );

        // `(x_B·y_Q)·z_Q = x_B·(y_Q·z_Q)`, which is the right-hand sample.
        let flat = rmul(d, mirror_pair, zq);
        let nested = {
            let tail = rmul(d, yq, zq);
            rmul(d, xb, tail)
        };
        let regroup = d.lemma(rat.mul_assoc, &[xb, yq, zq]);
        let head = rmul(d, pair_term, za);
        let source = rsub(d, rat, head, flat);
        let goal_quantity = rsub(d, rat, head, nested);
        let moved = rcongr(d, flat, nested, regroup, &|d, t| rsub(d, rat, head, t));
        let total_bound = div_succ_at(d, p, total_numerator, n);
        rat_eq_rewrite(d, source, goal_quantity, moved, estimate, &|d, t| {
            within(d, p, t, total_bound)
        })
    };

    let witness = d.lam_fv(n_fv, nat, at_index);
    let body = d.lemma(p.equiv_of_bounded, &[left, right, total_numerator, witness]);
    let value = {
        let with_z = d.lam_fv(z_fv, carrier, body);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, left, right);
        let with_z = d.pi_fv(z_fv, carrier, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_assoc,
        uparams: vec![],
        ty,
        value,
    })
}

/// `mul_le_mul_of_nonneg_left : ∀ x y z, le zero x → le y z →
/// le (mul x y) (mul x z)` — one of the 22, **verbatim**.
///
/// The only one of the eight that is not an estimate at all. Once
/// [`declare_left_distrib`] and [`declare_mul_congr`] exist it is the textbook
/// argument, and every step is an application of a law already proved:
/// `z − y ≥ 0`, so `x·(z − y) ≥ 0` by `mul_nonneg`, and `x·z` is
/// `Equiv`-equal to `x·y + x·(z − y)`, which is at least `x·y`. That is why the
/// costing put it downstream of `left_distrib` rather than budgeting a fourth
/// index estimate for it — and why doing `left_distrib` first was worth two of
/// the three remaining laws.
fn declare_mul_le_mul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let czero = d.kernel().const_(p.zero, vec![]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let first_ty = d.const_app(p.le, &[czero, x]);
    let second_ty = d.const_app(p.le, &[y, z]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let negated = d.const_app(p.neg, &[y]);
    let gap = cadd(d, p, z, negated);
    let cancelled = cadd(d, p, y, negated);

    // `0 ≤ z − y`.
    let nonneg_gap = {
        let reflexive = d.lemma(p.le_refl, &[negated]);
        let shifted = d.lemma(p.add_le_add, &[y, z, negated, negated, h2, reflexive]);
        let cancel = d.lemma(p.add_neg, &[y]);
        let gap_refl = d.lemma(p.equiv_refl, &[gap]);
        d.lemma(
            p.le_congr,
            &[cancelled, czero, gap, gap, cancel, gap_refl, shifted],
        )
    };
    let scaled_gap = cmul(d, p, x, gap);
    let nonneg_scaled = d.lemma(p.mul_nonneg, &[x, gap, h1, nonneg_gap]);

    // `Equiv (y + (z − y)) z`.
    let combined = cadd(d, p, y, gap);
    let plain_sum = cadd(d, p, y, z);
    let regrouped = cadd(d, p, plain_sum, negated);
    let mirrored_sum = cadd(d, p, z, y);
    let swapped = cadd(d, p, mirrored_sum, negated);
    let nested = cadd(d, p, z, cancelled);
    let padded = cadd(d, p, z, czero);
    let restored = {
        let assoc = d.lemma(p.add_assoc, &[y, z, negated]);
        let opened = d.lemma(p.equiv_symm, &[regrouped, combined, assoc]);
        let commute = d.lemma(p.add_comm, &[y, z]);
        let negated_refl = d.lemma(p.equiv_refl, &[negated]);
        let reordered = d.lemma(
            p.add_congr,
            &[
                plain_sum,
                mirrored_sum,
                negated,
                negated,
                commute,
                negated_refl,
            ],
        );
        let regroup = d.lemma(p.add_assoc, &[z, y, negated]);
        let z_refl = d.lemma(p.equiv_refl, &[z]);
        let cancel = d.lemma(p.add_neg, &[y]);
        let collapse = d.lemma(p.add_congr, &[z, z, cancelled, czero, z_refl, cancel]);
        let trim = d.lemma(p.add_zero, &[z]);
        let (_, proof) = equiv_chain(
            d,
            p,
            combined,
            &[
                (regrouped, opened),
                (swapped, reordered),
                (nested, regroup),
                (padded, collapse),
                (z, trim),
            ],
        );
        proof
    };

    // `Equiv (x·z) (x·y + x·(z − y))`.
    let scaled_left = cmul(d, p, x, y);
    let scaled_right = cmul(d, p, x, z);
    let scaled_combined = cmul(d, p, x, combined);
    let expanded = cadd(d, p, scaled_left, scaled_gap);
    let opened = {
        let distrib = d.lemma(p.left_distrib, &[x, y, gap]);
        let x_refl = d.lemma(p.equiv_refl, &[x]);
        let congr = d.lemma(p.mul_congr, &[x, x, combined, z, x_refl, restored]);
        let back = d.lemma(p.equiv_symm, &[scaled_combined, scaled_right, congr]);
        d.lemma(
            p.equiv_trans,
            &[scaled_right, scaled_combined, expanded, back, distrib],
        )
    };

    // `x·y ≤ x·y + x·(z − y)`, then move the right-hand side back to `x·z`.
    let body = {
        let reflexive = d.lemma(p.le_refl, &[scaled_left]);
        let grown = d.lemma(
            p.add_le_add,
            &[
                scaled_left,
                scaled_left,
                czero,
                scaled_gap,
                reflexive,
                nonneg_scaled,
            ],
        );
        let padded_left = cadd(d, p, scaled_left, czero);
        let trim = d.lemma(p.add_zero, &[scaled_left]);
        let sum_refl = d.lemma(p.equiv_refl, &[expanded]);
        let trimmed = d.lemma(
            p.le_congr,
            &[
                padded_left,
                scaled_left,
                expanded,
                expanded,
                trim,
                sum_refl,
                grown,
            ],
        );
        let back = d.lemma(p.equiv_symm, &[scaled_right, expanded, opened]);
        let left_refl = d.lemma(p.equiv_refl, &[scaled_left]);
        d.lemma(
            p.le_congr,
            &[
                scaled_left,
                scaled_left,
                expanded,
                scaled_right,
                left_refl,
                back,
                trimmed,
            ],
        )
    };

    let value = {
        let with_second = d.lam_fv(h2_fv, second_ty, body);
        let with_first = d.lam_fv(h1_fv, first_ty, with_second);
        let with_z = d.lam_fv(z_fv, carrier, with_first);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = d.const_app(p.le, &[scaled_left, scaled_right]);
        let after_second = d.arrow(second_ty, conclusion);
        let after_first = d.arrow(first_ty, after_second);
        let with_z = d.pi_fv(z_fv, carrier, after_first);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_le_mul_of_nonneg_left,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the laws ---------------------------------------------------------------

/// `of_rat_mul : ∀ q r, Equiv (mul (ofRat q) (ofRat r)) (ofRat (q·r))`.
///
/// **The homomorphism, and the reason the laws below are not vacuous.** Both
/// sides sample the *same closed rational* at every index — the embedding is a
/// constant sequence, so the product's index shift never matters — and the
/// proof is `Eq.refl`. That is precisely what makes it a good witness: it pins
/// `CReal.mul` to `Rat.mul` on the whole of the embedded `ℚ`, which no
/// degenerate product satisfies.
fn declare_of_rat_mul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = crate::rat_prelude::ops::rat_ty(d);
    let nat = d.nat_ty();

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let left = embed(d, p, q);
    let right = embed(d, p, r);
    let product = cmul(d, p, left, right);
    let scalar = rmul(d, q, r);
    let embedded = embed(d, p, scalar);

    let pointwise = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = rrefl(d, scalar);
        let _ = n;
        d.lam_fv(n_fv, nat, body)
    };
    let body = d.lemma(p.equiv_of_pointwise, &[product, embedded, pointwise]);
    let value = {
        let with_r = d.lam_fv(r_fv, carrier, body);
        d.lam_fv(q_fv, carrier, with_r)
    };
    let ty = {
        let claim = equiv(d, p, product, embedded);
        let with_r = d.pi_fv(r_fv, carrier, claim);
        d.pi_fv(q_fv, carrier, with_r)
    };
    let _ = rat;
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_rat_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// `mul_zero` and `mul_comm` — the two of the eight that are **pointwise**.
///
/// `mul x zero` samples `x_j · 0`, which `Rat.mul_zero` collapses to `0` at
/// every index; and `mul x y` and `mul y x` sample at indices that differ only
/// by `Nat.add_comm` inside `CReal.mulShift`, so one `ℕ` equation aligns them
/// and `Rat.mul_comm` finishes. Neither needs any analysis, and neither
/// discriminates — both hold of the constant-`zero` product, which is what
/// [`declare_discrimination`] is for.
fn declare_pointwise_laws(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    // mul_zero : Equiv (mul x zero) zero.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let czero = d.kernel().const_(p.zero, vec![]);
        let product = cmul(d, p, x, czero);
        let pointwise = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let shift = mul_shift(d, p, x, czero);
            let index = mul_index(d, shift, n);
            let point = sample(d, p, x, index);
            let body = d.lemma(rat.mul_zero, &[point]);
            d.lam_fv(n_fv, nat, body)
        };
        let body = d.lemma(p.equiv_of_pointwise, &[product, czero, pointwise]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let claim = equiv(d, p, product, czero);
            d.pi_fv(x_fv, carrier, claim)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mul_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // mul_comm : Equiv (mul x y) (mul y x).
    {
        let nat_prelude = p.rat.int.nat;
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let left = cmul(d, p, x, y);
        let right = cmul(d, p, y, x);
        let pointwise = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let shift = mul_shift(d, p, x, y);
            let mirrored = mul_shift(d, p, y, x);
            let index = mul_index(d, shift, n);
            let mirrored_index = mul_index(d, mirrored, n);
            let a = sample(d, p, x, index);
            let b = sample(d, p, y, index);
            let swapped = rmul(d, b, a);
            let commute = d.lemma(rat.mul_comm, &[a, b]);
            let bx = bound_of(d, p, x);
            let by = bound_of(d, p, y);
            let plain = NatOps::add(d, bx, by);
            let mirrored_plain = NatOps::add(d, by, bx);
            let shift_eq = {
                let inner = d.lemma(nat_prelude.add_comm, &[bx, by]);
                NatOps::congr(d, plain, mirrored_plain, inner, &|d, t| d.succ(t))
            };
            let index_eq = nat_eq_to_rat(d, shift, mirrored, shift_eq, &|d, t| {
                let moved = mul_index(d, t, n);
                let sy = sample(d, p, y, moved);
                let sx = sample(d, p, x, moved);
                rmul(d, sy, sx)
            });
            let target = {
                let sy = sample(d, p, y, mirrored_index);
                let sx = sample(d, p, x, mirrored_index);
                rmul(d, sy, sx)
            };
            let product = rmul(d, a, b);
            let body = rtrans(d, product, swapped, target, commute, index_eq);
            d.lam_fv(n_fv, nat, body)
        };
        let body = d.lemma(p.equiv_of_pointwise, &[left, right, pointwise]);
        let value = {
            let with_y = d.lam_fv(y_fv, carrier, body);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let claim = equiv(d, p, left, right);
            let with_y = d.pi_fv(y_fv, carrier, claim);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mul_comm,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Eq Rat (mul (Rat.neg a) (Rat.neg a)) (mul a a)`.
///
/// `neg_mul(a, neg a)` turns the left factor's sign around, `mul_neg(a, a)`
/// does the same for the right one hiding inside it, and `neg_neg` cancels
/// the resulting double negation. Returns `(lhs, rhs, proof)` so a caller can
/// chain `proof` against a further `Eq lhs' lhs` or `Eq rhs rhs''` without
/// reconstructing either side and risking a syntactically different (if
/// defeq) term.
fn sq_neg_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let neg_a = rneg(d, a);
    let lhs0 = rmul(d, neg_a, neg_a);
    let step1 = d.lemma(rat.neg_mul, &[a, neg_a]); // lhs0 = neg (mul a (neg a))
    let mul_a_nega = rmul(d, a, neg_a);
    let mid1 = rneg(d, mul_a_nega);
    let aa = rmul(d, a, a);
    let neg_aa = rneg(d, aa);
    let step2raw = d.lemma(rat.mul_neg, &[a, a]); // mul a (neg a) = neg (mul a a)
    let step2 = rcongr(d, mul_a_nega, neg_aa, step2raw, &|d, t| rneg(d, t));
    let mid2 = rneg(d, neg_aa);
    let step3 = d.lemma(rat.neg_neg, &[aa]); // neg (neg (mul a a)) = mul a a
    let (_, proof) = rchain(d, lhs0, &[(mid1, step1), (mid2, step2), (aa, step3)]);
    (lhs0, aa, proof)
}

/// `CReal.neg_mul_neg : ∀ x, Equiv (mul (neg x) (neg x)) (mul x x)`.
///
/// **Not pointwise.** `CReal.bound x` reads `Int.natAbs (Rat.num (seq x 0))`,
/// and `seq (neg x) 0` is `Rat.neg (seq x 0)`, so `bound (neg x)` and
/// `bound x` are not the *same term* — negation changes the representative.
/// They are, however, provably **equal naturals** (`Int.natAbs_neg`), which
/// is what this proof spends most of its length on: once `mulShift (neg x)
/// (neg x) = mulShift x x` is a `Nat` equation, both products sample at a
/// value-equal index and [`nat_eq_to_rat`] lifts that into a `Rat` equation
/// between the two samples, exactly the way [`declare_pointwise_laws`]'s
/// `mul_comm` proof lifts `Nat.add_comm` across `mulShift`. The sign
/// cancellation itself ([`sq_neg_eq`]) is the easy half.
fn declare_neg_mul_neg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let neg_x = d.const_app(p.neg, &[x]);
    let product1 = cmul(d, p, neg_x, neg_x);
    let product2 = cmul(d, p, x, x);

    // bound (neg x) = bound x, via Int.natAbs_neg at the index-0 numerator.
    let zero_nat = d.num(0);
    let s0 = sample(d, p, x, zero_nat);
    let q0 = num(d, s0);
    let int_p = p.rat.int;
    let neg_q0 = d.ineg(q0);
    let natabs_neg_q0 = d.const_app(int_p.nat_abs, &[neg_q0]);
    let natabs_q0 = d.const_app(int_p.nat_abs, &[q0]);
    let magnitude_eq = d.lemma(int_p.nat_abs_neg, &[q0]);
    let bound_negx = bound_of(d, p, neg_x);
    let bound_x = bound_of(d, p, x);
    let bound_eq = NatOps::congr(d, natabs_neg_q0, natabs_q0, magnitude_eq, &|d, t| d.succ(t));

    // mulShift (neg x) (neg x) = mulShift x x.
    let sum1 = NatOps::add(d, bound_negx, bound_negx);
    let sum_mid = NatOps::add(d, bound_x, bound_negx);
    let sum2 = NatOps::add(d, bound_x, bound_x);
    let step_a = NatOps::congr(d, bound_negx, bound_x, bound_eq, &|d, t| {
        NatOps::add(d, t, bound_negx)
    });
    let step_b = NatOps::congr(d, bound_negx, bound_x, bound_eq, &|d, t| {
        NatOps::add(d, bound_x, t)
    });
    let (_, sum_eq) = NatOps::chain(d, sum1, &[(sum_mid, step_a), (sum2, step_b)]);
    let shift1 = mul_shift(d, p, neg_x, neg_x);
    let shift2 = mul_shift(d, p, x, x);
    let shift_eq = NatOps::congr(d, sum1, sum2, sum_eq, &|d, t| d.succ(t));

    // Both products sample at the same (value-equal) index.
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let j1 = mul_index(d, shift1, n);
    let j2 = mul_index(d, shift2, n);
    let index_eq = NatOps::congr(d, shift1, shift2, shift_eq, &|d, t| mul_index(d, t, n));

    let a1 = sample(d, p, x, j1);
    let a2 = sample(d, p, x, j2);
    let base_eq = nat_eq_to_rat(d, j1, j2, index_eq, &|d, t| sample(d, p, x, t));

    let (lhs0, aa1, sqneg_eq) = sq_neg_eq(d, p, a1);
    let a1a2 = rmul(d, a1, a2);
    let aa2 = rmul(d, a2, a2);
    let sq_step1 = rcongr(d, a1, a2, base_eq, &|d, t| rmul(d, a1, t));
    let sq_step2 = rcongr(d, a1, a2, base_eq, &|d, t| rmul(d, t, a2));
    let sq_eq = rtrans(d, aa1, a1a2, aa2, sq_step1, sq_step2);
    let pointwise_n = rtrans(d, lhs0, aa1, aa2, sqneg_eq, sq_eq);

    let pointwise = d.lam_fv(n_fv, nat, pointwise_n);
    let body = d.lemma(p.equiv_of_pointwise, &[product1, product2, pointwise]);
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = {
        let claim = equiv(d, p, product1, product2);
        d.pi_fv(x_fv, carrier, claim)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.neg_mul_neg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Eq Rat (mul (Rat.abs a) (Rat.abs a)) (mul a a)` — the `abs` analogue of
/// [`sq_neg_eq`], via [`mul_self_abs_rat`]. Returns `(lhs, rhs, proof)` for
/// the same reason `sq_neg_eq` does: a caller chains `proof` against a
/// further `Eq lhs' lhs` / `Eq rhs rhs''` without reconstructing either side
/// and risking a syntactically different (if defeq) term.
fn sq_abs_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let magnitude = rabs(d, rat, a);
    let lhs = rmul(d, magnitude, magnitude);
    let rhs = rmul(d, a, a);
    let proof = mul_self_abs_rat(d, rat, a);
    (lhs, rhs, proof)
}

/// `CReal.mul_self_abs : ∀ x, Equiv (mul (abs x) (abs x)) (mul x x)`.
///
/// The unconditional half of the constructive triangle-inequality gap (see
/// [`super::CRealPrelude::mul_self_abs`]'s doc comment for why `le_of_sq_le`
/// alone cannot close `Complex.abs_add_le`).
///
/// **Not called from [`declare_product`] above, unlike every other law in
/// this file.** `CReal.abs` is `CReal.max x (CReal.neg x)`
/// ([`super::lattice`]), declared in the *lattice* phase (ADR-0519 R5), which
/// runs strictly after the *product* phase (R2) that owns this file
/// (`build_creal_prelude_uncached` calls `product::declare_product` before
/// `lattice::declare_lattice`). Referencing `p.abs` from inside
/// `declare_product` itself is an `UnknownConst` — declaration order matters
/// (this crate's own multi-agent notes call this out explicitly): the
/// dispatcher must run after everything it references, so `creal.rs`'s
/// top-level builder calls this function directly, after
/// `lattice::declare_lattice`, not through [`declare_product`].
///
/// **Not pointwise**, exactly like [`declare_neg_mul_neg`] just above:
/// `CReal.bound` reads `Int.natAbs (Rat.num (seq x 0))`, and `seq (abs x) 0`
/// is `Rat.abs (seq x 0)`, so `bound (abs x)` and `bound x` are not the
/// *same* term. They are, as there, **provably equal naturals** — but via a
/// `Rat.le_or_lt` case split ([`abs_num_nat_abs_eq`]) rather than
/// `Int.natAbs_neg` alone, because `Rat.abs`/`Rat.max` decide on the sign of
/// an *integer* rather than perform a fixed sign-flip: nothing about `abs x`
/// reduces at a symbolic `x` without first knowing which side of zero its
/// representative is on. Once `mulShift (abs x) (abs x) = mulShift x x` is a
/// `Nat` equation, both products sample at a value-equal index and
/// [`nat_eq_to_rat`] lifts that into a `Rat` equation between the two
/// samples — [`declare_neg_mul_neg`]'s structure, verbatim. The sign
/// cancellation itself ([`sq_abs_eq`]) is the easy half.
pub(super) fn declare_mul_self_abs(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let abs_x = d.const_app(p.abs, &[x]);
    let product1 = cmul(d, p, abs_x, abs_x);
    let product2 = cmul(d, p, x, x);

    // bound (abs x) = bound x, via a Rat.le_or_lt case split at the index-0
    // numerator.
    let zero_nat = d.num(0);
    let s0 = sample(d, p, x, zero_nat);
    let int_p = p.rat.int;
    let q0 = num(d, s0);
    let abs_s0 = rabs(d, p.rat, s0);
    let num_abs_q0 = num(d, abs_s0);
    let natabs_abs_q0 = d.const_app(int_p.nat_abs, &[num_abs_q0]);
    let natabs_q0 = d.const_app(int_p.nat_abs, &[q0]);
    let magnitude_eq = abs_num_nat_abs_eq(d, p.rat, s0);
    let bound_absx = bound_of(d, p, abs_x);
    let bound_x = bound_of(d, p, x);
    let bound_eq = NatOps::congr(d, natabs_abs_q0, natabs_q0, magnitude_eq, &|d, t| d.succ(t));

    // mulShift (abs x) (abs x) = mulShift x x.
    let sum1 = NatOps::add(d, bound_absx, bound_absx);
    let sum_mid = NatOps::add(d, bound_x, bound_absx);
    let sum2 = NatOps::add(d, bound_x, bound_x);
    let step_a = NatOps::congr(d, bound_absx, bound_x, bound_eq, &|d, t| {
        NatOps::add(d, t, bound_absx)
    });
    let step_b = NatOps::congr(d, bound_absx, bound_x, bound_eq, &|d, t| {
        NatOps::add(d, bound_x, t)
    });
    let (_, sum_eq) = NatOps::chain(d, sum1, &[(sum_mid, step_a), (sum2, step_b)]);
    let shift1 = mul_shift(d, p, abs_x, abs_x);
    let shift2 = mul_shift(d, p, x, x);
    let shift_eq = NatOps::congr(d, sum1, sum2, sum_eq, &|d, t| d.succ(t));

    // Both products sample at the same (value-equal) index.
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let j1 = mul_index(d, shift1, n);
    let j2 = mul_index(d, shift2, n);
    let index_eq = NatOps::congr(d, shift1, shift2, shift_eq, &|d, t| mul_index(d, t, n));

    let a1 = sample(d, p, x, j1);
    let a2 = sample(d, p, x, j2);
    let base_eq = nat_eq_to_rat(d, j1, j2, index_eq, &|d, t| sample(d, p, x, t));

    let (lhs0, aa1, sqabs_eq) = sq_abs_eq(d, p, a1);
    let a1a2 = rmul(d, a1, a2);
    let aa2 = rmul(d, a2, a2);
    let sq_step1 = rcongr(d, a1, a2, base_eq, &|d, t| rmul(d, a1, t));
    let sq_step2 = rcongr(d, a1, a2, base_eq, &|d, t| rmul(d, t, a2));
    let sq_eq = rtrans(d, aa1, a1a2, aa2, sq_step1, sq_step2);
    let pointwise_n = rtrans(d, lhs0, aa1, aa2, sqabs_eq, sq_eq);

    let pointwise = d.lam_fv(n_fv, nat, pointwise_n);
    let body = d.lemma(p.equiv_of_pointwise, &[product1, product2, pointwise]);
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = {
        let claim = equiv(d, p, product1, product2);
        d.pi_fv(x_fv, carrier, claim)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_self_abs,
        uparams: vec![],
        ty,
        value,
    })
}

/// `mul_one : ∀ x, Equiv (mul x one) x`.
///
/// The first of the eight that is **not** pointwise: `mul x one` samples `x` at
/// `(c+1)·n + c` where `x` samples it at `n`, so the two sides agree at no
/// index. One `Rat.mul_one` removes the unit factor and the rest is regularity
/// plus [`index_modulus_le`] — the deeper sample's modulus is at most the
/// shallower one's, at one denominator.
fn declare_mul_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let cone = d.kernel().const_(p.one, vec![]);
    let product = cmul(d, p, x, cone);

    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let shift = mul_shift(d, p, x, cone);
        let index = mul_index(d, shift, n);
        let deep = sample(d, p, x, index);
        let shallow = sample(d, p, x, n);
        let quantity = rsub(d, rat, deep, shallow);
        let spread = modulus(d, p, index, n);
        let regular = d.lemma(p.regular, &[x, index, n]);

        let one_atom = div_succ(d, p, 1, n);
        let deep_atom = div_succ(d, p, 1, index);
        let one_nat = d.num(1);
        let deep_le = index_le(d, p, one_nat, shift, n);
        let shallow_refl = d.lemma(rat.le_refl, &[one_atom]);
        let widened = d.lemma(
            rat.add_le_add,
            &[
                deep_atom,
                one_atom,
                one_atom,
                one_atom,
                deep_le,
                shallow_refl,
            ],
        );
        let doubled = radd(d, one_atom, one_atom);
        let target_bound = div_succ(d, p, 2, n);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let order = rat_eq_rewrite(d, doubled, target_bound, fuse, widened, &|d, t| {
            rle(d, rat, spread, t)
        });
        let weakened = weaken(d, p, quantity, spread, target_bound, regular, order);

        let unit = rone(d, rat);
        let scaled = rmul(d, deep, unit);
        let collapse = d.lemma(rat.mul_one, &[deep]);
        let restore = rsymm(d, scaled, deep, collapse);
        let target_quantity = rsub(d, rat, scaled, shallow);
        let moved = rcongr(d, deep, scaled, restore, &|d, t| rsub(d, rat, t, shallow));
        let at_quantity = rat_eq_rewrite(d, quantity, target_quantity, moved, weakened, &|d, t| {
            within(d, p, t, target_bound)
        });
        d.lam_fv(n_fv, nat, at_quantity)
    };
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = {
        let claim = equiv(d, p, product, x);
        d.pi_fv(x_fv, carrier, claim)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `sq_nonneg` and `mul_nonneg`.
///
/// `sq_nonneg` is free: `x_j·x_j ≥ 0` at `ℚ` and `0 ≤ 2/(n+1)`, so the order's
/// slack is never touched. `mul_nonneg` is not: `0 ≤ x` over the reals does
/// **not** say any sample of `x` is non-negative — only that each sits above
/// `−2/(j+1)` — so the product's lower bound has to trade that residue against
/// the other factor's canonical magnitude. That is
/// [`Rat.neg_mul_le_of_bounds`](crate::RatPrelude::neg_mul_le_of_bounds), and
/// the resulting `2/(j+1) · (c+1)/1` fuses back to exactly `2/(n+1)`.
fn declare_nonneg_laws(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let czero = d.kernel().const_(p.zero, vec![]);

    // sq_nonneg : le zero (mul x x).
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let product = cmul(d, p, x, x);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let at_index = {
            let shift = mul_shift(d, p, x, x);
            let index = mul_index(d, shift, n);
            let point = sample(d, p, x, index);
            let square = rmul(d, point, point);
            let bound = div_succ(d, p, 2, n);
            let two_nat = d.num(2);
            let nonneg = d.lemma(rat.sq_nonneg, &[point]);
            let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[square, nonneg]);
            let negated = rneg(d, square);
            let zero_rat = rzero(d, rat);
            let slack = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, n]);
            let chained = d.lemma(rat.le_trans, &[negated, zero_rat, bound, nonpos, slack]);
            restate_as_difference(d, p, square, n, chained)
        };
        let value = {
            let over_n = d.lam_fv(n_fv, nat, at_index);
            d.lam_fv(x_fv, carrier, over_n)
        };
        let ty = {
            let claim = d.const_app(p.le, &[czero, product]);
            d.pi_fv(x_fv, carrier, claim)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sq_nonneg,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // mul_nonneg : le zero x → le zero y → le zero (mul x y).
    {
        let nat_prelude = p.rat.int.nat;
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let first_ty = d.const_app(p.le, &[czero, x]);
        let second_ty = d.const_app(p.le, &[czero, y]);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let product = cmul(d, p, x, y);

        let at_index = {
            let shift = mul_shift(d, p, x, y);
            let index = mul_index(d, shift, n);
            let a = sample(d, p, x, index);
            let b = sample(d, p, y, index);
            let raw = rmul(d, a, b);
            let zero_nat = d.num(0);
            let two_nat = d.num(2);
            let residue = div_succ(d, p, 2, index);
            let successor = d.succ(shift);
            let shared = div_succ_at(d, p, successor, zero_nat);

            let residue_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, index]);
            let shared_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[successor, zero_nat]);
            let lower_a = lower_bound_of_nonneg(d, p, x, index, h1);
            let lower_b = lower_bound_of_nonneg(d, p, y, index, h2);
            let upper_a = shared_upper_bound(d, p, x, y, index, true);
            let upper_b = shared_upper_bound(d, p, x, y, index, false);
            let estimate = d.lemma(
                rat.neg_mul_le_of_bounds,
                &[
                    a,
                    b,
                    residue,
                    shared,
                    residue_nonneg,
                    shared_nonneg,
                    lower_a,
                    upper_a,
                    lower_b,
                    upper_b,
                ],
            );
            let bound = rmul(d, residue, shared);
            let negated_bound = rneg(d, bound);
            let flipped = d.lemma(rat.neg_le_neg, &[negated_bound, raw, estimate]);
            let doubled = rneg(d, negated_bound);
            let restore = d.lemma(rat.neg_neg, &[bound]);
            let negated_product = rneg(d, raw);
            let unwrapped = rat_eq_rewrite(d, doubled, bound, restore, flipped, &|d, t| {
                rle(d, rat, negated_product, t)
            });

            // `2/(j+1) · (c+1)/1 = (c+1)/1 · 2/(j+1) = (2·(c+1))/(j+1)
            //  = 2/1 · (c+1)/(j+1) = 2/1 · 1/(n+1) = 2/(n+1)`.
            let target = div_succ(d, p, 2, n);
            let collapse = {
                let swap = d.lemma(rat.mul_comm, &[residue, shared]);
                let swapped = rmul(d, shared, residue);
                let fuse = d.lemma(rat.nat_div_succ_mul, &[successor, two_nat, index]);
                let fused_numerator = NatOps::mul(d, successor, two_nat);
                let fused = div_succ_at(d, p, fused_numerator, index);
                let commute = d.lemma(nat_prelude.mul_comm, &[successor, two_nat]);
                let mirrored_numerator = NatOps::mul(d, two_nat, successor);
                let mirrored = div_succ_at(d, p, mirrored_numerator, index);
                let realign =
                    nat_eq_to_rat(d, fused_numerator, mirrored_numerator, commute, &|d, t| {
                        div_succ_at(d, p, t, index)
                    });
                let factored = {
                    let left = div_succ_at(d, p, two_nat, zero_nat);
                    let right = div_succ_at(d, p, successor, index);
                    rmul(d, left, right)
                };
                let split = {
                    let forward = d.lemma(rat.nat_div_succ_mul, &[two_nat, successor, index]);
                    rsymm(d, factored, mirrored, forward)
                };
                let inner = div_succ_at(d, p, successor, index);
                let one_n = div_succ(d, p, 1, n);
                let scale = d.lemma(rat.nat_div_succ_scale, &[shift, n]);
                let rescaled = rcongr(d, inner, one_n, scale, &|d, t| {
                    let left = div_succ_at(d, p, two_nat, zero_nat);
                    rmul(d, left, t)
                });
                let scaled_pair = {
                    let left = div_succ_at(d, p, two_nat, zero_nat);
                    rmul(d, left, one_n)
                };
                let one_nat = d.num(1);
                let final_fuse = d.lemma(rat.nat_div_succ_mul, &[two_nat, one_nat, n]);
                let final_numerator = NatOps::mul(d, two_nat, one_nat);
                let almost = div_succ_at(d, p, final_numerator, n);
                let trim = d.lemma(nat_prelude.mul_one, &[two_nat]);
                let tidy = nat_eq_to_rat(d, final_numerator, two_nat, trim, &|d, t| {
                    div_succ_at(d, p, t, n)
                });
                let (_, proof) = rchain(
                    d,
                    bound,
                    &[
                        (swapped, swap),
                        (fused, fuse),
                        (mirrored, realign),
                        (factored, split),
                        (scaled_pair, rescaled),
                        (almost, final_fuse),
                        (target, tidy),
                    ],
                );
                proof
            };
            let at_bound = rat_eq_rewrite(d, bound, target, collapse, unwrapped, &|d, t| {
                rle(d, rat, negated_product, t)
            });
            restate_as_difference(d, p, raw, n, at_bound)
        };
        let value = {
            let over_n = d.lam_fv(n_fv, nat, at_index);
            let with_second = d.lam_fv(h2_fv, second_ty, over_n);
            let with_first = d.lam_fv(h1_fv, first_ty, with_second);
            let with_y = d.lam_fv(y_fv, carrier, with_first);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let conclusion = d.const_app(p.le, &[czero, product]);
            let after_second = d.arrow(second_ty, conclusion);
            let after_first = d.arrow(first_ty, after_second);
            let with_y = d.pi_fv(y_fv, carrier, after_first);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mul_nonneg,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// Turn `Rat.le (−v) (2/(n+1))` into the `CReal.le zero _` body shape
/// `Rat.le (seq zero n − v) (2/(n+1))`.
fn restate_as_difference(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    value: ExprId,
    n: ExprId,
    proof: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_rat = rzero(d, rat);
    let negated = rneg(d, value);
    let bound = div_succ(d, p, 2, n);
    let difference = rsub(d, rat, zero_rat, value);
    let collapse = d.lemma(rat.zero_add, &[negated]);
    let restore = rsymm(d, difference, negated, collapse);
    rat_eq_rewrite(d, negated, difference, restore, proof, &|d, t| {
        rle(d, rat, t, bound)
    })
}

/// `−(2/(j+1)) ≤ seq x j` from `CReal.le zero x`.
fn lower_bound_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    j: ExprId,
    hypothesis: ExprId,
) -> ExprId {
    let rat = p.rat;
    let point = sample(d, p, x, j);
    let bound = div_succ(d, p, 2, j);
    let instance = d.apply(hypothesis, &[j]);
    let zero_rat = rzero(d, rat);
    let difference = rsub(d, rat, zero_rat, point);
    let negated = rneg(d, point);
    let collapse = d.lemma(rat.zero_add, &[negated]);
    let plain = rat_eq_rewrite(d, difference, negated, collapse, instance, &|d, t| {
        rle(d, rat, t, bound)
    });
    let flipped = d.lemma(rat.neg_le_neg, &[negated, bound, plain]);
    let doubled = rneg(d, negated);
    let restore = d.lemma(rat.neg_neg, &[point]);
    let negated_bound = rneg(d, bound);
    rat_eq_rewrite(d, doubled, point, restore, flipped, &|d, t| {
        rle(d, rat, negated_bound, t)
    })
}

/// `seq x j ≤ (mulShift x y + 1)/1` — the canonical bound of one factor,
/// widened to the shared bound both factors satisfy.
fn shared_upper_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    j: ExprId,
    first: bool,
) -> ExprId {
    let rat = p.rat;
    let nat = p.rat.int.nat;
    let target = if first { x } else { y };
    let point = sample(d, p, target, j);
    let own = bound_value(d, p, target);
    let own_numerator = magnitude_of(d, p, target);
    let other_numerator = magnitude_of(d, p, if first { y } else { x });
    let zero_nat = d.num(0);
    let witness = d.lemma(p.bound_within, &[target, j]);
    let (_, upper) = halves(d, p, point, own, witness);
    let grown = d.lemma(
        rat.nat_div_succ_le_add_left,
        &[own_numerator, other_numerator, zero_nat],
    );
    let summed = NatOps::add(d, own_numerator, other_numerator);
    let shift = mul_shift(d, p, x, y);
    let successor = d.succ(shift);
    let ordered = if first {
        magnitudes_sum(d, p, x, y)
    } else {
        let commute = d.lemma(nat.add_comm, &[own_numerator, other_numerator]);
        let mirrored = NatOps::add(d, other_numerator, own_numerator);
        let base = magnitudes_sum(d, p, x, y);
        NatOps::trans(d, summed, mirrored, successor, commute, base)
    };
    let widened = div_succ_at(d, p, summed, zero_nat);
    let shared = div_succ_at(d, p, successor, zero_nat);
    let aligned = nat_rewrite_prop(d, summed, successor, ordered, grown, &|d, t| {
        let moved = div_succ_at(d, p, t, zero_nat);
        rle(d, rat, own, moved)
    });
    let _ = widened;
    d.lemma(rat.le_trans, &[point, own, shared, upper, aligned])
}

/// `not_equiv_mul_one_one_zero : Not (Equiv (mul one one) zero)`.
///
/// The **discrimination** witness for the product. `mul_zero`, `sq_nonneg` and
/// `mul_comm` all hold, with empty footprints, of `fun _ _ => zero`; this
/// refuses it by computation, through [`declare_of_rat_mul`] — `1·1` is `1` in
/// `ℚ`, so `mul one one` is `Equiv`-equal to `one`, and `Equiv zero one` is
/// already refuted by `CReal.Equiv.not_zero_one`.
fn declare_discrimination(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let cone = d.kernel().const_(p.one, vec![]);
    let czero = d.kernel().const_(p.zero, vec![]);
    let product = cmul(d, p, cone, cone);
    let claim = equiv(d, p, product, czero);
    let stmt = d.not(claim);

    let unit = rone(d, rat);
    let homomorphism = d.lemma(p.of_rat_mul, &[unit, unit]);
    let square = rmul(d, unit, unit);
    let collapse = d.lemma(rat.mul_one, &[unit]);
    let at_one = rat_eq_rewrite(d, square, unit, collapse, homomorphism, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, product, embedded)
    });

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let reversed = d.lemma(p.equiv_symm, &[product, czero, h]);
    let chained = d.lemma(p.equiv_trans, &[czero, product, cone, reversed, at_one]);
    let absurd = d.lemma(p.not_zero_one, &[chained]);
    let value = d.lam_fv(h_fv, claim, absurd);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.not_equiv_mul_one_one_zero,
        uparams: vec![],
        ty: stmt,
        value,
    })
}
