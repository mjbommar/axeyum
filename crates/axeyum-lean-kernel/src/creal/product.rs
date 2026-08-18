//! **`CReal.mul`**, and the five of the 22 ordered-ring laws that follow from
//! it directly (ADR-0468 phase R2, continued).
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
//! extracted before it can be used. With ADR-0468's fixed modulus there is
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
//! ## What is *not* here, and why the discrimination witness matters
//!
//! `mul_assoc`, `left_distrib` and `mul_le_mul_of_nonneg_left` are not proved
//! here; neither is `mul_congr`. All three of the former compare two products
//! sampled at *different* indices — `mul x (add y z)` and `add (mul x y)
//! (mul x z)` do not agree on any index and their shifts are not even equal as
//! naturals — so each needs the arbitrary-third-index estimate `Equiv.trans`
//! runs on, plus the Archimedean lemma. They are costed in the module docs of
//! `creal` and in the lane status file.
//!
//! Of the five that *are* here, three —
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
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{
    num, radd, rat_eq_rewrite, rchain, rcongr, rle, rmul, rneg, rone, rrefl, rsymm, rtrans, rzero,
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
    declare_of_rat_mul(d, p)?;
    declare_pointwise_laws(d, p)?;
    declare_mul_one(d, p)?;
    declare_nonneg_laws(d, p)?;
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
fn mul_shift(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul_shift, &[x, y])
}

/// `(c+1)·n + c`, the index `CReal.mul` samples at.
fn mul_index(d: &mut IntDev<'_>, c: ExprId, n: ExprId) -> ExprId {
    let factor = d.succ(c);
    let scaled = NatOps::mul(d, factor, n);
    NatOps::add(d, scaled, c)
}

/// `CReal.mul x y`.
fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

/// From `h : Eq Nat a b`, derive `Eq Rat (f a) (f b)`.
///
/// The `ℕ → ℚ` companion of
/// [`IntDev::nat_eq_to_int`](crate::int_prelude::ops::IntDev). Every index
/// identity in this module — `bound x + bound y = bound y + bound x`,
/// `Kx + Ky = c + 1` — is a `ℕ` equation whose consequence is a `ℚ` one.
fn nat_eq_to_rat(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = NatOps::eq_motive(d, a, &|d, x| {
        let fx = f(d, x);
        crate::rat_prelude::ops::req(d, fa, fx)
    });
    let refl_case = rrefl(d, fa);
    NatOps::transport(d, a, motive, refl_case, b, h)
}

/// From `h : Eq Nat a b` and a proof of `motive a`, derive `motive b`.
fn nat_rewrite_prop(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    proof: ExprId,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let built = NatOps::eq_motive(d, a, motive);
    NatOps::transport(d, a, built, proof, b, h)
}

/// `Eq Nat (1 + j) (succ j)` — `Nat.add j 1` **is** `succ j`, so one
/// `Nat.add_comm` is the whole proof.
fn one_add_eq_succ(d: &mut IntDev<'_>, p: CRealPrelude, j: ExprId) -> ExprId {
    let nat = p.rat.int.nat;
    let one_nat = d.num(1);
    d.lemma(nat.add_comm, &[one_nat, j])
}

/// `Rat.le (natDivSucc 1 ((c+1)·n + c)) (natDivSucc 1 n)` — the deeper sample's
/// modulus is at most the shallower one's.
///
/// **Not** antitonicity of `natDivSucc`: the numerator is widened `1 ↦ 1 + c`
/// at the *same* index, and then `natDivSucc_scale` reads
/// `(c+1)/((c+1)·n + c + 1)` as `1/(n+1)`. One denominator throughout, for a
/// shift `c` that varies with the two factors.
fn index_modulus_le(d: &mut IntDev<'_>, p: CRealPrelude, c: ExprId, n: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let index = mul_index(d, c, n);
    let base = div_succ(d, p, 1, index);
    let widened_numerator = NatOps::add(d, one_nat, c);
    let grown = d.lemma(rat.nat_div_succ_le_add_left, &[one_nat, c, index]);
    let successor = d.succ(c);
    let commute = one_add_eq_succ(d, p, c);
    let at_successor =
        nat_rewrite_prop(d, widened_numerator, successor, commute, grown, &|d, t| {
            let moved = div_succ_at(d, p, t, index);
            rle(d, rat, base, moved)
        });
    let scaled = div_succ_at(d, p, successor, index);
    let scale = d.lemma(rat.nat_div_succ_scale, &[c, n]);
    let target = div_succ(d, p, 1, n);
    rat_eq_rewrite(d, scaled, target, scale, at_successor, &|d, t| {
        rle(d, rat, base, t)
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
        let deep_le = index_modulus_le(d, p, shift, n);
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
        let one_nat = d.num(1);
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
