//! **`CReal.UniformlyContinuousOn`** (ADR-0512, continuing phase R11): a
//! modulus-carrying notion of uniform continuity on an interval, and the
//! bridge from it to the sequential [`CReal.ContinuousAt`](super::CRealPrelude::continuous_at)
//! [`declare_convergence`](super::convergence::declare_convergence) already
//! has.
//!
//! ## Why the modulus is data, not a proof
//!
//! [`CReal.pos_bound_of_lt`](super::CRealPrelude::pos_bound_of_lt)'s own
//! module documentation already states the house rule: `0 < x` and its
//! `Nat`-indexed witness are the *same proposition*, and the witness still
//! cannot be pulled out of the `Exists` and used to build anything in
//! `Type` — which is exactly why [`CReal.inv`](super::CRealPrelude::inv)
//! takes its modulus `k : Nat` as an explicit argument rather than deriving
//! it from a `PosBound` proof. A `Prop`-level `∀ε∃δ` reading of uniform
//! continuity has the identical shape and hits the identical wall: the
//! finite-sweep argument this predicate exists to support needs `δ` as
//! `Nat` *data* (a partition width, a sampling index), and `Exists.rec`'s
//! target must not depend on the witness when the target is a `Type`. So
//! `UniformlyContinuousOn` is declared in `Type`, with `modulus : Nat →
//! Nat` a field exactly the way [`CReal.seq`](super::CRealPrelude::seq) is
//! a field of `CReal` itself — the one-constructor-inductive shape (a
//! `Type`-valued data field plus a dependent `Prop`-valued spec field,
//! large elimination for the first projection) is copied from `CReal`'s
//! own carrier ([`super::declare_carrier`]), not invented fresh.
//!
//! ## Why the spec is real-valued, not the canonical-sample idiom
//!
//! [`CReal.Converges`](super::CRealPrelude::converges) and
//! [`CReal.Cauchy`](super::CRealPrelude::cauchy) both compare *samples at a
//! shared index* — the convention [`convergence`](super::convergence)'s own
//! module documentation explains and prefers. That convention was tried
//! here first and abandoned: it ties "which term" to "which accuracy index"
//! as the same `n`, and every attempt to route a
//! [`CReal.Converges`](super::CRealPrelude::converges) witness (rate `K/(n+1)`,
//! a *fixed* `K`) through a modulus spec of that shape needs the hypothesis
//! and the conclusion read at two *different* indices — `g n`'s own
//! accuracy is intrinsically `O(1/n)` and cannot be improved by sampling
//! elsewhere, so the "same index" convention has no slack to spend. The
//! real-valued form `le (abs (x − y)) (ofRat (1/(modulus n + 1))) → le
//! (abs (F x − F y)) (ofRat (1/(n+1)))` is index-free in `x, y`: `le`'s own
//! definition is already a `∀m, …` statement, so a proof is free to unfold
//! it at whichever sample index it already needs — the unfolding
//! `uniformly_continuous_imp_continuous_at` (the bridge to `ContinuousAt`,
//! not landed here — see below) would need.
//!
//! ## What this slice lands, and what it does not
//!
//! Landed: the predicate, its two projections (large elimination for
//! `modulus`, ordinary elimination for `spec`), two witnesses (`id` and
//! `const`) that show the predicate is not vacuous, and the closure lemma
//! `uniformly_continuous_add` (`F`, `G` uniformly continuous on `[a,b]` ⇒
//! so is `fun r => F r + G r`, combined modulus `mF(2n+1) + mG(2n+1)`,
//! unblocked by `Rat.natDivSucc_antitone` — see that declaration's own doc
//! comment for the full argument). **Not landed: `uniformly_continuous_mul`,
//! a named `BoundedOn` predicate, scalar multiplication `fun r => a * r`,
//! and the theorem tying `UniformlyContinuousOn` back to `ContinuousAt`.**
//! All were attempted or considered; none is force-fit, for concrete,
//! verified reasons recorded here rather than gestured at.
//!
//! **`uniformly_continuous_mul` and `BoundedOn`.** `hasDerivative_mul`
//! (`derivative.rs`) needs both factors' magnitude bounded on `[a,b]`, and
//! that hypothesis is built by a *local* `bounded_on_ty` helper there — an
//! inline `∀z, a≤z→z≤b→|h z|≤(k+1)/(0+1)` Pi type, never promoted to a
//! kernel-level named predicate. A `mul` closure lemma for
//! `UniformlyContinuousOn` needs the SAME two-factor magnitude-bound
//! composition `hasDerivative_mul`'s own proof builds by hand (`rescale_index`
//! / `fold_index0_first` / `fold_index0_second` / `mul_modulus_components` /
//! `fuse_three_equal_bounds`, several hundred lines), because closeness of a
//! product needs `|F(x)G(x) − F(y)G(y)| ≤ |F(x)||G(x)−G(y)| + |G(y)||F(x)−F(y)|`
//! — a genuine product-of-bounds estimate, not a triangle inequality — and
//! that machinery is private to `derivative.rs`, out of this slice's file
//! boundary. Naming `BoundedOn` as a `Definition` (transparent, so it stays
//! defeq to `bounded_on_ty`'s inline shape and a closure theorem about it
//! could still be applied at `derivative.rs`'s existing call sites) is the
//! right design if this is picked back up, but building `bounded_on_mul`
//! itself is a slice on the order of `hasDerivative_mul` itself, not a
//! same-session extension of `uniformly_continuous_add`.
//!
//! **This blocker is not on the induction path to `hasDerivative_pow` at
//! general `n`, and that is worth stating plainly.** `hasDerivative_cube`
//! (`derivative.rs`) already proves `r*(r*r) = id(r)*sq(r)` by applying
//! `hasDerivative_mul` with `F := id`, so its continuity hypothesis is
//! `uniformly_continuous_id` — landed since this file's first slice. An
//! induction `pow (n+1) = id * pow n` keeps `F := id` at *every* step, so
//! it needs `uniformly_continuous_id` again and again, never
//! `uniformly_continuous_mul`. What it DOES need at every step is
//! boundedness of `id`, of `pow(·,n)`, and of `pow(·,n)`'s own derivative on
//! `[a,b]` — i.e. exactly the `BoundedOn`-closure-under-`mul` gap above, not
//! a `UniformlyContinuousOn` one. So the general power rule's real
//! remaining blocker is `bounded_on_mul`, not `uniformly_continuous_mul`.
//!
//! **Scalar multiplication.** The natural route needs `mul a (add x (neg
//! y))` related to `add (mul a x) (neg (mul a y))` — i.e. a `mul`-vs-`neg`
//! commutation (`a·(x−y) = a·x − a·y` in a form usable at the `CReal.le`
//! level). Nothing in [`CRealPrelude`] states this directly; the nearest
//! facts are [`CReal.left_distrib`](super::CRealPrelude::left_distrib)
//! (distributes over `add`, not `neg`) and
//! [`CReal.neg_mul_neg`](super::CRealPrelude::neg_mul_neg) (both factors
//! negated, not one). Deriving `mul a (neg y) ~ neg (mul a y)` from these —
//! e.g. by showing `mul a y` and `mul a (neg y)` are both additive inverses
//! of one another via `left_distrib` + `add_neg` + `mul_zero`, then
//! invoking uniqueness of the additive inverse — is plausible but is
//! *itself* an unwritten lemma, not a two-line consequence of what already
//! exists. Landing scalar multiplication honestly needs that lemma first;
//! forcing the proof through without it is exactly the "grinding on a
//! false shortcut" the previous slice's IVT counterexample was praised for
//! refusing to do.
//!
//! **`uniformly_continuous_imp_continuous_at`.** The obstruction is
//! concrete: closing it needs, for the *fixed* `K` a `Converges` witness
//! supplies and an *arbitrary* `modulus : Nat → Nat` from the hypothesis, a
//! `Nat` `k` (as a function of the outer index `n`) with `K/(n+1) ≤
//! 1/(modulus k + 1)` — a genuine `Nat`-division search (`k` on the order
//! of `n/K`), not a rearrangement. [`Rat.natDivSucc`](crate::RatPrelude::nat_div_succ)
//! being "not antitone in its index" is flagged as a *deliberately
//! avoided* cost in [`convergence`](super::convergence)'s own module
//! documentation (the comment on `Rat.natDivSucc_scale`), and every
//! existing estimate in this file is engineered to need only a *fixed*,
//! closed-form index — which is exactly what defeated the scalar-mult
//! witness above too (its own modulus, `(c+1)·n + c`, is one of those
//! closed forms, and `nat_div_succ_scale` turns it into an *equality* with
//! no search at all; an *arbitrary* modulus has no such form). Closing this
//! needs `Nat.div`/`Nat.mod` machinery (present in `nat_prelude`, e.g.
//! `Nat.div_mod_bounds`) chained through a four-term real-vs-rational
//! telescope relating a `Converges` witness's sample at `n` to the real
//! distance between `g n` and its limit — worked out on paper to the point
//! of confidence it is provable, but not built: it did not fit this slice.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::ring_helpers::add4_comm;
use super::{CRealPrelude, cle, creal_ty, embed, equiv, halves, sample};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    den, den_pos, den_z, nat_eq_to_rat, nat_rewrite_prop, normalize, num, one_le_succ, radd,
    rat_eq_rewrite, rat_ty, rchain, rcongr, rle, rneg, rsymm, rzero,
};

/// Admit `CReal.UniformlyContinuousOn` (the carrier and its two
/// projections), two witnesses (`id` and `const`), and the closure lemma
/// `uniformly_continuous_add`. See the module documentation for why scalar
/// multiplication, `uniformly_continuous_mul`, a named `BoundedOn`
/// predicate, and the bridge to `ContinuousAt` are not landed here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_uniform_continuity(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_carrier(d, p)?;
    declare_projections(d, p)?;
    declare_uniformly_continuous_id(d, p)?;
    declare_uniformly_continuous_const(d, p)?;
    declare_uniformly_continuous_add(d, p)?;
    declare_uniformly_continuous_neg(d, p)?;
    declare_uniformly_continuous_sub(d, p)?;
    declare_bucket_index(d, p)?;
    declare_bucket_index_floor(d, p)?;
    declare_bucket_clamp_upper(d, p)?;
    declare_bucket_clamp_lower(d, p)?;
    declare_bucket_index_bound(d, p)?;
    declare_sample_upper_bound(d, p)?;
    declare_sample_lower_bound(d, p)
}

// --- the bucket-index primitive ---------------------------------------------
//
// `CReal.bounded_of_uniformly_continuous`'s covering argument (see the
// module documentation) needs, for a point `z` in `[a, b]` and a target
// resolution `k` (step `1/(Nat.succ k)`), a COMPUTABLE `Nat` index of the
// sample point nearest `z − a` from below. `CReal.archimedean`'s own `∃`
// witness cannot be pulled into `Type` (the identical `Exists`-into-`Type`
// wall the module documentation's own house rule states), and picking the
// nearest of infinitely many candidates by comparison is not even
// well-posed (`CReal.le` is undecidable) -- so this has to be a genuine
// projection off ONE rational sample, the same move `CReal.bound` makes,
// not a search.

/// `CReal.bucketIndex w k : Nat` -- the computable "which sample bucket does
/// `w` fall into" primitive.
///
/// Recipe verbatim from `creal/sqrt.rs::declare_sqrt_approx`'s own
/// `sqrtApprox` (see that declaration's own doc comment for the identical
/// five-line shape): sample `w` at accuracy index `j := k1*k1` (`k1 :=
/// Nat.succ k`, so `j` is finer than the target resolution `1/k1` by a full
/// factor of `k1`), clamp to `≥ 0` via `Rat.max _ Rat.zero` (`Rat.max`
/// dispatches on the representation, no case split on `w`'s sign), read the
/// clamped sample's numerator/denominator as `Nat`s (`Int.natAbs` is
/// *exact* here, not merely an upper bound, because clamping already made
/// the numerator nonnegative), and floor-divide `numerator * k1` by the
/// denominator via the total `Nat.div`.
fn bucket_index(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId, k: ExprId) -> ExprId {
    let k1 = d.succ(k);
    let j = NatOps::mul(d, k1, k1);
    let sample_w = sample(d, p, w, j);
    let zero_rat = rzero(d, p.rat);
    let q_pos = d.const_app(p.rat.max, &[sample_w, zero_rat]);
    let numerator = num(d, q_pos);
    let a = d.const_app(p.rat.int.nat_abs, &[numerator]);
    let b = den(d, q_pos);
    let scaled = NatOps::mul(d, a, k1);
    NatOps::div(d, scaled, b)
}

/// Admit `CReal.bucketIndex : CReal → Nat → Nat`. See the module
/// documentation and [`bucket_index`]'s own doc comment for the recipe;
/// **no closeness property is proved for it in this slice** -- see
/// [`CRealPrelude::bucket_index`]'s own doc comment for exactly what
/// remains.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bucket_index(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = bucket_index(d, p, w, k);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(w_fv, carrier, with_k)
    };
    let ty = {
        let inner = d.arrow(nat, nat);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.bucket_index,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 44),
    })
}

// --- the bucket-index closeness property ------------------------------------
//
// `bucket_index`'s own doc comment names exactly what is missing: a proof
// that the sample point `bucketIndex w k` lands within one step of `w`. What
// follows is the sharpest, hypothesis-free form of that fact: `w`'s own
// clamped sample `q := Rat.max (seq w j) 0` (`j` the accuracy index
// `bucketIndex` itself samples at) is sandwiched between the two adjacent
// multiples of `step := 1/(k+1)` that bracket `bucketIndex w k` --
//
//   natDivSucc (bucketIndex w k) k  <=  q  <=  natDivSucc (succ (bucketIndex w k)) k
//
// exactly the floor-division guarantee `Nat.div_mod_bounds` gives for
// `Nat.div (a*k1) b` (`a`, `b` being `q`'s own clamped numerator/denominator),
// read back into `Rat.le` by cross-multiplying against `Rat.natDivSucc`'s own
// `normalize`d representative (`Rat.normalize_cross`). No hypothesis on `w`'s
// SIGN is needed anywhere here: `q` is clamped to `>= 0` unconditionally
// (`Rat.le_max_right`), which is exactly what makes `a := natAbs (num q)` an
// EXACT — not merely bounding — read of `num q`. (A sign hypothesis on `w`
// only starts to matter for the FURTHER step of relating `q` back to `w`
// itself through `w`'s own regularity — see [`declare_bucket_clamp_upper`]/
// [`declare_bucket_clamp_lower`] below, where it is exactly the `le zero w`
// hypothesis the lower half needs and the upper half does not.)

/// `Nat.le i n`, from `hlt : Nat.lt i n` (defeq `Nat.le (succ i) n`). Local
/// copy of `monotone.rs`'s private `nat_le_of_lt` (see that file's own copy
/// for why this small helper is duplicated rather than shared).
fn bucket_nat_le_of_lt(d: &mut IntDev<'_>, i: ExprId, n: ExprId, hlt: ExprId) -> ExprId {
    let np = d.prelude();
    let succ_i = d.succ(i);
    let step = d.const_app(np.le_succ, &[i]);
    d.const_app(np.le_trans, &[i, succ_i, n, step, hlt])
}

/// Admit [`CRealPrelude::bucket_index_floor_lower`] and
/// [`CRealPrelude::bucket_index_floor_upper`]. See the section documentation
/// above for the statement and the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_bucket_index_floor(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = p.rat.int.nat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // --- shared setup, rebuilt identically to `bucket_index`'s own recipe --
    let k1 = d.succ(k);
    let j = NatOps::mul(d, k1, k1);
    let w_j = sample(d, p, w, j);
    let zero_rat = rzero(d, rat);
    let q = d.const_app(rat.max, &[w_j, zero_rat]);

    let q_nonneg = d.lemma(rat.le_max_right, &[w_j, zero_rat]); // Rat.le 0 q
    let num_q = num(d, q);
    let num_q_nonneg = d.lemma(rat.int_nonneg_of_nonneg, &[q, q_nonneg]); // Int.le 0 (num q)
    let a = d.const_app(rat.int.nat_abs, &[num_q]);
    let num_q_eq = d.lemma(rat.int.of_nat_nat_abs_of_nonneg, &[num_q, num_q_nonneg]); // Eq Int (ofNat a) (num q)
    let b = den(d, q);
    let bz = den_z(d, q);

    let scaled = NatOps::mul(d, a, k1);
    let m = NatOps::div(d, scaled, b); // == bucket_index w k, by construction

    // --- b = succ (pred b), so `div_mod_exec` (which needs a literal succ
    // divisor) applies ------------------------------------------------------
    let b_pos = den_pos(d, q); // Nat.le 1 b == Nat.lt 0 b
    let b_pred = d.pred(b);
    let succ_b_pred = d.succ(b_pred);
    let heq_b = d.lemma(nat.succ_pred_of_pos, &[b, b_pos]); // Eq Nat b succ_b_pred
    let heq_b_symm = d.symm(b, succ_b_pred, heq_b); // Eq Nat succ_b_pred b

    // --- `Nat.div_mod_bounds` at `succ_b_pred`, rewritten back to `b` -------
    let dme = d.lemma(nat.div_mod_exec, &[b_pred, scaled]);
    let div_sbp = d.div(scaled, succ_b_pred);
    let mod_sbp = d.modulo(scaled, succ_b_pred);
    let bounds_sbp = d.lemma(
        nat.div_mod_bounds,
        &[succ_b_pred, scaled, div_sbp, mod_sbp, dme],
    );

    let and_name = p.rat.int.logic.and;
    let motive_body = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let div_x = d.div(scaled, x);
        let lhs = NatOps::mul(d, x, div_x);
        let le1 = NatOps::le(d, lhs, scaled);
        let succ_div = d.succ(div_x);
        let rhs2 = NatOps::mul(d, x, succ_div);
        let lt1 = NatOps::lt(d, scaled, rhs2);
        d.const_app(and_name, &[le1, lt1])
    };
    let bounds_b = d.nat_rewrite(succ_b_pred, b, heq_b_symm, bounds_sbp, &motive_body);

    let le1_b = {
        let lhs = NatOps::mul(d, b, m);
        NatOps::le(d, lhs, scaled)
    };
    let m1 = d.succ(m);
    let rhs2_b = NatOps::mul(d, b, m1);
    let lt1_b = NatOps::lt(d, scaled, rhs2_b);
    let lower_b = d.and_left(le1_b, lt1_b, bounds_b); // Nat.le (b*m) scaled
    let upper_b_strict = d.and_right(le1_b, lt1_b, bounds_b); // Nat.lt scaled (b*m1)
    let upper_b = bucket_nat_le_of_lt(d, scaled, rhs2_b, upper_b_strict); // Nat.le scaled (b*m1)

    let az = d.of_nat(a);
    let k1z = d.of_nat(k1);
    let mz = d.of_nat(m);
    let m1z = d.of_nat(m1);

    let pos_k1 = one_le_succ(d, k);

    // --- rep_m := natDivSucc m k, rep_m1 := natDivSucc m1 k -----------------
    let rep_m = normalize(d, mz, k1, pos_k1);
    let nm = num(d, rep_m);
    let dm = den(d, rep_m);
    let dm_z = den_z(d, rep_m);
    let cross_m = d.lemma(rat.normalize_cross, &[mz, k1, pos_k1]); // Eq (nm*k1z) (mz*dm_z)

    let rep_m1 = normalize(d, m1z, k1, pos_k1);
    let nm1 = num(d, rep_m1);
    let dm1 = den(d, rep_m1);
    let dm1_z = den_z(d, rep_m1);
    let cross_m1 = d.lemma(rat.normalize_cross, &[m1z, k1, pos_k1]); // Eq (nm1*k1z) (m1z*dm1_z)

    // ============ LOWER: Rat.le rep_m q  (i.e. natDivSucc m k <= q) ========
    let lower_final = {
        let bz_mz = d.imul(bz, mz);
        let az_k1z = d.imul(az, k1z);
        let scaled_lower = d.lemma(rat.int_mul_le_mul_right, &[bz_mz, az_k1z, dm, lower_b]);
        // : Int.le ((bz*mz)*dm_z) ((az*k1z)*dm_z)
        let lhs0 = d.imul(bz_mz, dm_z);
        let rhs0 = d.imul(az_k1z, dm_z);

        let mz_dmz = d.imul(mz, dm_z);
        let nm_k1z = d.imul(nm, k1z);
        let cross_m_rev = d.isymm(nm_k1z, mz_dmz, cross_m); // Eq (mz*dm_z)(nm*k1z)

        let bz_mzdmz = d.imul(bz, mz_dmz);
        let assoc_l1 = d.lemma(rat.int.mul_assoc, &[bz, mz, dm_z]); // Eq (lhs0)(bz*(mz*dm_z))
        let bz_nmk1z = d.imul(bz, nm_k1z);
        let step_l2 = d.icongr(mz_dmz, nm_k1z, cross_m_rev, &|d, t| d.imul(bz, t));
        let bz_nm = d.imul(bz, nm);
        let bz_nm_k1z = d.imul(bz_nm, k1z);
        let assoc_l3 = d.lemma(rat.int.mul_assoc, &[bz, nm, k1z]); // Eq ((bz*nm)*k1z)(bz*(nm*k1z))
        let assoc_l3_rev = d.isymm(bz_nm_k1z, bz_nmk1z, assoc_l3);
        let comm_l4 = d.lemma(rat.int.mul_comm, &[bz, nm]); // Eq (bz*nm)(nm*bz)
        let nm_bz = d.imul(nm, bz);
        let nm_bz_k1z = d.imul(nm_bz, k1z);
        let step_l4 = d.icongr(bz_nm, nm_bz, comm_l4, &|d, t| d.imul(t, k1z));

        let (target_lhs, eq_lhs) = d.ichain(
            lhs0,
            &[
                (bz_mzdmz, assoc_l1),
                (bz_nmk1z, step_l2),
                (bz_nm_k1z, assoc_l3_rev),
                (nm_bz_k1z, step_l4),
            ],
        );

        let k1z_dmz = d.imul(k1z, dm_z);
        let az_k1zdmz = d.imul(az, k1z_dmz);
        let assoc_r1 = d.lemma(rat.int.mul_assoc, &[az, k1z, dm_z]); // Eq (rhs0)(az*(k1z*dm_z))
        let dmz_k1z = d.imul(dm_z, k1z);
        let az_dmzk1z = d.imul(az, dmz_k1z);
        let comm_r2 = d.lemma(rat.int.mul_comm, &[k1z, dm_z]); // Eq (k1z*dm_z)(dm_z*k1z)
        let step_r2 = d.icongr(k1z_dmz, dmz_k1z, comm_r2, &|d, t| d.imul(az, t));
        let az_dmz = d.imul(az, dm_z);
        let az_dmz_k1z = d.imul(az_dmz, k1z);
        let assoc_r3 = d.lemma(rat.int.mul_assoc, &[az, dm_z, k1z]); // Eq ((az*dm_z)*k1z)(az*(dm_z*k1z))
        let assoc_r3_rev = d.isymm(az_dmz_k1z, az_dmzk1z, assoc_r3);

        let (target_rhs, eq_rhs) = d.ichain(
            rhs0,
            &[
                (az_k1zdmz, assoc_r1),
                (az_dmzk1z, step_r2),
                (az_dmz_k1z, assoc_r3_rev),
            ],
        );

        let motive1 = d.ieq_motive(lhs0, &|d, x| d.ile(x, rhs0));
        let step1 = d.itransport(lhs0, motive1, scaled_lower, target_lhs, eq_lhs);
        let motive2 = d.ieq_motive(rhs0, &|d, x| d.ile(target_lhs, x));
        let step2 = d.itransport(rhs0, motive2, step1, target_rhs, eq_rhs);
        // step2 : Int.le ((nm*bz)*k1z) ((az*dm_z)*k1z)

        let lower_cross = d.lemma(
            rat.int_le_of_mul_le_mul_right,
            &[nm_bz, az_dmz, k1, pos_k1, step2],
        );
        // : Int.le (nm*bz) (az*dm_z)

        let eq_az_dmz = d.icongr(az, num_q, num_q_eq, &|d, t| d.imul(t, dm_z));
        let num_q_dmz = d.imul(num_q, dm_z);
        let motive3 = d.ieq_motive(az_dmz, &|d, x| d.ile(nm_bz, x));
        d.itransport(az_dmz, motive3, lower_cross, num_q_dmz, eq_az_dmz)
        // : Int.le (nm*bz) (num_q*dm_z)  ==defeq==  Rat.le rep_m q
    };

    // ============ UPPER: Rat.le q rep_m1  (i.e. q <= natDivSucc m1 k) ======
    let upper_final = {
        let az_k1z = d.imul(az, k1z);
        let bz_m1z = d.imul(bz, m1z);
        let scaled_upper = d.lemma(rat.int_mul_le_mul_right, &[az_k1z, bz_m1z, dm1, upper_b]);
        // : Int.le ((az*k1z)*dm1_z) ((bz*m1z)*dm1_z)
        let lhs0 = d.imul(az_k1z, dm1_z);
        let rhs0 = d.imul(bz_m1z, dm1_z);

        let k1z_dm1z = d.imul(k1z, dm1_z);
        let az_k1zdm1z = d.imul(az, k1z_dm1z);
        let assoc_l1 = d.lemma(rat.int.mul_assoc, &[az, k1z, dm1_z]); // Eq (lhs0)(az*(k1z*dm1_z))
        let dm1z_k1z = d.imul(dm1_z, k1z);
        let az_dm1zk1z = d.imul(az, dm1z_k1z);
        let comm_l2 = d.lemma(rat.int.mul_comm, &[k1z, dm1_z]); // Eq (k1z*dm1_z)(dm1_z*k1z)
        let step_l2 = d.icongr(k1z_dm1z, dm1z_k1z, comm_l2, &|d, t| d.imul(az, t));
        let az_dm1z = d.imul(az, dm1_z);
        let az_dm1z_k1z = d.imul(az_dm1z, k1z);
        let assoc_l3 = d.lemma(rat.int.mul_assoc, &[az, dm1_z, k1z]); // Eq ((az*dm1_z)*k1z)(az*(dm1_z*k1z))
        let assoc_l3_rev = d.isymm(az_dm1z_k1z, az_dm1zk1z, assoc_l3);

        let (target_lhs, eq_lhs) = d.ichain(
            lhs0,
            &[
                (az_k1zdm1z, assoc_l1),
                (az_dm1zk1z, step_l2),
                (az_dm1z_k1z, assoc_l3_rev),
            ],
        );

        let m1z_dm1z = d.imul(m1z, dm1_z);
        let bz_m1zdm1z = d.imul(bz, m1z_dm1z);
        let assoc_r1 = d.lemma(rat.int.mul_assoc, &[bz, m1z, dm1_z]); // Eq (rhs0)(bz*(m1z*dm1_z))
        let nm1_k1z = d.imul(nm1, k1z);
        let cross_m1_rev = d.isymm(nm1_k1z, m1z_dm1z, cross_m1); // Eq (m1z*dm1_z)(nm1*k1z)
        let bz_nm1k1z = d.imul(bz, nm1_k1z);
        let step_r2 = d.icongr(m1z_dm1z, nm1_k1z, cross_m1_rev, &|d, t| d.imul(bz, t));
        let bz_nm1 = d.imul(bz, nm1);
        let bz_nm1_k1z = d.imul(bz_nm1, k1z);
        let assoc_r3 = d.lemma(rat.int.mul_assoc, &[bz, nm1, k1z]); // Eq ((bz*nm1)*k1z)(bz*(nm1*k1z))
        let assoc_r3_rev = d.isymm(bz_nm1_k1z, bz_nm1k1z, assoc_r3);
        let comm_r4 = d.lemma(rat.int.mul_comm, &[bz, nm1]); // Eq (bz*nm1)(nm1*bz)
        let nm1_bz = d.imul(nm1, bz);
        let nm1_bz_k1z = d.imul(nm1_bz, k1z);
        let step_r4 = d.icongr(bz_nm1, nm1_bz, comm_r4, &|d, t| d.imul(t, k1z));

        let (target_rhs, eq_rhs) = d.ichain(
            rhs0,
            &[
                (bz_m1zdm1z, assoc_r1),
                (bz_nm1k1z, step_r2),
                (bz_nm1_k1z, assoc_r3_rev),
                (nm1_bz_k1z, step_r4),
            ],
        );

        let motive1 = d.ieq_motive(lhs0, &|d, x| d.ile(x, rhs0));
        let step1 = d.itransport(lhs0, motive1, scaled_upper, target_lhs, eq_lhs);
        let motive2 = d.ieq_motive(rhs0, &|d, x| d.ile(target_lhs, x));
        let step2 = d.itransport(rhs0, motive2, step1, target_rhs, eq_rhs);
        // step2 : Int.le ((az*dm1_z)*k1z) ((nm1*bz)*k1z)

        let upper_cross = d.lemma(
            rat.int_le_of_mul_le_mul_right,
            &[az_dm1z, nm1_bz, k1, pos_k1, step2],
        );
        // : Int.le (az*dm1_z) (nm1*bz)

        let eq_az_dm1z = d.icongr(az, num_q, num_q_eq, &|d, t| d.imul(t, dm1_z));
        let num_q_dm1z = d.imul(num_q, dm1_z);
        let motive3 = d.ieq_motive(az_dm1z, &|d, x| d.ile(x, nm1_bz));
        d.itransport(az_dm1z, motive3, upper_cross, num_q_dm1z, eq_az_dm1z)
        // : Int.le (num_q*dm1_z) (nm1*bz)  ==defeq==  Rat.le q rep_m1
    };

    // --- close both theorems -------------------------------------------------
    let m_named = d.const_app(p.bucket_index, &[w, k]);
    let rep_m_named = d.const_app(rat.nat_div_succ, &[m_named, k]);
    let lower_ty_body = rle(d, rat, rep_m_named, q);
    let lower_ty = {
        let with_k = d.pi_fv(k_fv, nat_ty, lower_ty_body);
        d.pi_fv(w_fv, carrier, with_k)
    };
    let lower_value = {
        let with_k = d.lam_fv(k_fv, nat_ty, lower_final);
        d.lam_fv(w_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bucket_index_floor_lower,
        uparams: vec![],
        ty: lower_ty,
        value: lower_value,
    })?;

    let m1_named = d.succ(m_named);
    let rep_m1_named = d.const_app(rat.nat_div_succ, &[m1_named, k]);
    let upper_ty_body = rle(d, rat, q, rep_m1_named);
    let upper_ty = {
        let with_k = d.pi_fv(k_fv, nat_ty, upper_ty_body);
        d.pi_fv(w_fv, carrier, with_k)
    };
    let upper_value = {
        let with_k = d.lam_fv(k_fv, nat_ty, upper_final);
        d.lam_fv(w_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bucket_index_floor_upper,
        uparams: vec![],
        ty: upper_ty,
        value: upper_value,
    })
}

// --- relating the bucket sample back to `w` itself --------------------------
//
// `bucketIndexFloorLower`/`Upper` sandwich the CLAMPED sample `q := Rat.max
// (seq w j) 0` between two adjacent multiples of `1/(k+1)`. That pins the
// grid point relative to `q`, not relative to `w` itself -- and `w` is what
// `bounded_of_uniformly_continuous`'s covering argument actually needs close
// to a sample point. This section supplies exactly that: `w` is within a
// small, FIXED (not shrinking-in-`k`) multiple of `1/(j+1)` of `q`, in both
// directions. `j := (k+1)*(k+1)` throughout, matching [`bucket_index`].

/// `Eq ((a+b)+c) ((a+c)+b)` -- swap the last two summands of a
/// left-associated `Rat` sum. Private to this section; the two three-term
/// reorderings [`declare_bucket_clamp_upper`] and
/// [`declare_bucket_clamp_lower`] need are both instances of this or
/// [`radd3_swap_first`], never a fresh assoc/comm derivation each.
fn radd3_swap_last(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let ab = radd(d, a, b);
    let bc = radd(d, b, c);
    let cb = radd(d, c, b);
    let ac = radd(d, a, c);
    let start = radd(d, ab, c);
    let s1 = radd(d, a, bc);
    let h1 = d.lemma(rat.add_assoc, &[a, b, c]); // (a+b)+c = a+(b+c)
    let s2 = radd(d, a, cb);
    let comm_bc = d.lemma(rat.add_comm, &[b, c]); // b+c = c+b
    let h2 = rcongr(d, bc, cb, comm_bc, &|d, t| radd(d, a, t));
    let s3 = radd(d, ac, b);
    let assoc_ac_b = d.lemma(rat.add_assoc, &[a, c, b]); // (a+c)+b = a+(c+b)
    let h3 = rsymm(d, s3, s2, assoc_ac_b);
    rchain(d, start, &[(s1, h1), (s2, h2), (s3, h3)])
}

/// `Eq (a+(b+c)) (b+(a+c))` -- swap the first two summands of a
/// right-associated `Rat` sum.
fn radd3_swap_first(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let bc = radd(d, b, c);
    let ab = radd(d, a, b);
    let ba = radd(d, b, a);
    let ac = radd(d, a, c);
    let start = radd(d, a, bc);
    let s1 = radd(d, ab, c);
    let assoc_ab_c = d.lemma(rat.add_assoc, &[a, b, c]); // (a+b)+c = a+(b+c)
    let h1 = rsymm(d, s1, start, assoc_ab_c);
    let s2 = radd(d, ba, c);
    let comm_ab = d.lemma(rat.add_comm, &[a, b]); // a+b = b+a
    let h2 = rcongr(d, ab, ba, comm_ab, &|d, t| radd(d, t, c));
    let s3 = radd(d, b, ac);
    let h3 = d.lemma(rat.add_assoc, &[b, a, c]); // (b+a)+c = b+(a+c)
    rchain(d, start, &[(s1, h1), (s2, h2), (s3, h3)])
}

/// `w`, `k`, `j := (succ k)*(succ k)`, `wj := seq w j`, `q := max wj 0`.
/// Shared setup, rebuilt identically to [`bucket_index`]'s own recipe (and
/// to [`declare_bucket_index_floor`]'s), so `q`/`j` here are the SAME terms
/// those declarations' own statements mention.
fn clamp_setup(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    w: ExprId,
    k: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let k1 = d.succ(k);
    let j = NatOps::mul(d, k1, k1);
    let wj = sample(d, p, w, j);
    let zero_rat = rzero(d, p.rat);
    let q = d.const_app(p.rat.max, &[wj, zero_rat]);
    (j, wj, q)
}

/// Admit [`CRealPrelude::bucket_clamp_upper`]. See that field's own doc
/// comment for the statement and [`CRealPrelude::bucket_clamp_lower`]'s for
/// why this half needs no sign hypothesis on `w`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_bucket_clamp_upper(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let (j, wj, q) = clamp_setup(d, p, w, k);
    let zero_rat = rzero(d, rat);
    let one_nat = d.num(1);
    let bound2j = div_succ(d, p, 2, j);
    let target = radd(d, q, bound2j);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let wn = sample(d, p, w, n);

    let div1n = div_succ(d, p, 1, n);
    let div1j = div_succ(d, p, 1, j);
    let modulus_nj = radd(d, div1n, div1j);

    // `w`'s own regularity: `seq w n - seq w j <= 1/(n+1)+1/(j+1)`.
    let reg = d.lemma(p.regular, &[w, n, j]);
    let diff_nj = rsub(d, rat, wn, wj);
    let (_, reg_upper) = halves(d, p, diff_nj, modulus_nj, reg);
    let wn_le_wj_plus_mod = d.lemma(rat.le_of_sub_le, &[wn, wj, modulus_nj, reg_upper]);
    // : Rat.le wn (radd wj modulus_nj)

    // `seq w j <= q` unconditionally (`Rat.le_max_left`), so
    // `wn <= wj+modulus_nj <= q+modulus_nj`.
    let le_max_left_wj = d.lemma(rat.le_max_left, &[wj, zero_rat]);
    let refl_mod = d.lemma(rat.le_refl, &[modulus_nj]);
    let step_a = d.lemma(
        rat.add_le_add,
        &[wj, q, modulus_nj, modulus_nj, le_max_left_wj, refl_mod],
    );
    let wj_plus_mod = radd(d, wj, modulus_nj);
    let q_plus_mod = radd(d, q, modulus_nj);
    let wn_le_q_plus_mod = d.lemma(
        rat.le_trans,
        &[wn, wj_plus_mod, q_plus_mod, wn_le_wj_plus_mod, step_a],
    );

    // Widen `1/(n+1)+1/(j+1)` up to `2/(n+1)+2/(j+1)`.
    let bound2n = div_succ(d, p, 2, n);
    let mono_n = d.lemma(rat.nat_div_succ_le_add_left, &[one_nat, one_nat, n]);
    let mono_j = d.lemma(rat.nat_div_succ_le_add_left, &[one_nat, one_nat, j]);
    let widen_mod = d.lemma(
        rat.add_le_add,
        &[div1n, bound2n, div1j, bound2j, mono_n, mono_j],
    );

    let refl_q = d.lemma(rat.le_refl, &[q]);
    let bn_bj = radd(d, bound2n, bound2j);
    let step_b = d.lemma(
        rat.add_le_add,
        &[q, q, modulus_nj, bn_bj, refl_q, widen_mod],
    );
    let q_bn_bj = radd(d, q, bn_bj);
    let wn_le_q_bn_bj = d.lemma(
        rat.le_trans,
        &[wn, q_plus_mod, q_bn_bj, wn_le_q_plus_mod, step_b],
    );
    // : Rat.le wn (radd q (radd bound2n bound2j))

    // Reorder `q + (bound2n + bound2j)` to `(q + bound2j) + bound2n`:
    // comm on the inner pair, then assoc (reversed) to move `bound2n` out.
    let bj_bn = radd(d, bound2j, bound2n);
    let comm1 = d.lemma(rat.add_comm, &[bound2n, bound2j]); // Eq bn_bj bj_bn
    let cong1 = rcongr(d, bn_bj, bj_bn, comm1, &|d, t| radd(d, q, t));
    let q_bj_bn = radd(d, q, bj_bn);
    let target_bn = radd(d, target, bound2n);
    let assoc1 = d.lemma(rat.add_assoc, &[q, bound2j, bound2n]); // Eq target_bn q_bj_bn
    let assoc1_rev = rsymm(d, target_bn, q_bj_bn, assoc1); // Eq q_bj_bn target_bn
    let (final_form, eq_final) = rchain(d, q_bn_bj, &[(q_bj_bn, cong1), (target_bn, assoc1_rev)]);

    let wn_le_final = rat_eq_rewrite(d, q_bn_bj, final_form, eq_final, wn_le_q_bn_bj, &|d, t| {
        rle(d, rat, wn, t)
    });
    // : Rat.le wn (radd target bound2n)
    let at_n = d.lemma(rat.sub_le_of_le, &[wn, target, bound2n, wn_le_final]);
    // : Rat.le (rsub wn target) bound2n

    let embedded_target = embed(d, p, target);
    let cle_stmt = cle(d, p, w, embedded_target);
    let ty = {
        let with_k = d.pi_fv(k_fv, nat_ty, cle_stmt);
        d.pi_fv(w_fv, carrier, with_k)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat_ty, at_n);
        let with_k = d.lam_fv(k_fv, nat_ty, with_n);
        d.lam_fv(w_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bucket_clamp_upper,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`CRealPrelude::bucket_clamp_lower`]. See that field's own doc
/// comment for the statement and for why `le zero w` is genuinely needed
/// here (unlike [`declare_bucket_clamp_upper`]'s half).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_bucket_clamp_lower(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let (j, wj, q) = clamp_setup(d, p, w, k);
    let zero_rat = rzero(d, rat);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let bound2j = div_succ(d, p, 2, j);
    let bound3j = div_succ(d, p, 3, j);
    let target2 = rsub(d, rat, q, bound3j);

    // `hzw : CReal.le CReal.zero w`.
    let czero = d.kernel().const_(p.zero, vec![]);
    let hzw_ty = cle(d, p, czero, w);
    let hzw_fv = d.fresh_fvar();
    let hzw = d.kernel().fvar(hzw_fv);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let wn = sample(d, p, w, n);

    // `hzw` at index `j`: `Rat.le (rsub (seq czero j) wj) bound2j`, which is
    // DEFEQ to `Rat.le zero_rat (radd wj bound2j)`'s premise shape --
    // `le_of_sub_le` is applied with `u := seq czero j` directly, and the
    // kernel's own defeq check (CReal.zero/ofRat/seq all unfold under
    // `ReducibilityHint::Regular`) is what identifies `seq czero j` with
    // `Rat.zero` at `add_declaration` time.
    let sample_czero_j = sample(d, p, czero, j);
    let hzw_at_j = d.apply(hzw, &[j]);
    let zero_le_wj_plus_b2j = d.lemma(rat.le_of_sub_le, &[sample_czero_j, wj, bound2j, hzw_at_j]);
    // : Rat.le sample_czero_j (radd wj bound2j)  ~defeq~  Rat.le zero_rat (radd wj bound2j)

    // branch1 : Rat.le wj (radd wj bound2j), via `add_le_add` + `add_zero`.
    let wj_plus_b2j = radd(d, wj, bound2j);
    let refl_wj = d.lemma(rat.le_refl, &[wj]);
    let nonneg_b2j = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, j]);
    let padded_wj = radd(d, wj, zero_rat);
    let widened1 = d.lemma(
        rat.add_le_add,
        &[wj, wj, zero_rat, bound2j, refl_wj, nonneg_b2j],
    );
    let trim1 = d.lemma(rat.add_zero, &[wj]);
    let branch1 = rat_eq_rewrite(d, padded_wj, wj, trim1, widened1, &|d, t| {
        rle(d, rat, t, wj_plus_b2j)
    });

    // `q <= wj + bound2j`, via `Rat.max_le` on branch1 and
    // `zero_le_wj_plus_b2j`.
    let q_le = d.lemma(
        rat.max_le,
        &[wj, zero_rat, wj_plus_b2j, branch1, zero_le_wj_plus_b2j],
    );

    // `w`'s regularity at `(j,n)`: `seq w j - seq w n <= 1/(j+1)+1/(n+1)`.
    let div1j = div_succ(d, p, 1, j);
    let div1n = div_succ(d, p, 1, n);
    let modulus_jn = radd(d, div1j, div1n);
    let reg2 = d.lemma(p.regular, &[w, j, n]);
    let diff_jn = rsub(d, rat, wj, wn);
    let (_, reg2_upper) = halves(d, p, diff_jn, modulus_jn, reg2);
    let wj_le_wn_plus_mod = d.lemma(rat.le_of_sub_le, &[wj, wn, modulus_jn, reg2_upper]);
    // : Rat.le wj (radd wn modulus_jn)

    // Combine: `q <= wj+bound2j <= (wn+modulus_jn)+bound2j`.
    let wn_plus_mod = radd(d, wn, modulus_jn);
    let refl_b2j = d.lemma(rat.le_refl, &[bound2j]);
    let step_b = d.lemma(
        rat.add_le_add,
        &[
            wj,
            wn_plus_mod,
            bound2j,
            bound2j,
            wj_le_wn_plus_mod,
            refl_b2j,
        ],
    );
    let big_rhs = radd(d, wn_plus_mod, bound2j);
    let q_le_big = d.lemma(rat.le_trans, &[q, wj_plus_b2j, big_rhs, q_le, step_b]);
    // : Rat.le q (radd (radd wn modulus_jn) bound2j)
    //         =  Rat.le q ((wn + (div1j+div1n)) + bound2j)

    // Regroup `(wn + (div1j+div1n)) + bound2j` -> `wn + ((div1j+div1n)+bound2j)`.
    let inner = radd(d, div1j, div1n);
    let assoc_wn = d.lemma(rat.add_assoc, &[wn, inner, bound2j]); // Eq big_rhs (wn+(inner+bound2j))
    let inner_plus_b2j = radd(d, inner, bound2j);
    let wn_inner_b2j = radd(d, wn, inner_plus_b2j);

    // Regroup `(div1j+div1n)+bound2j` -> `(div1j+bound2j)+div1n`.
    let (swapped_inner, eq_swap_inner) = radd3_swap_last(d, p, div1j, div1n, bound2j);
    let cong_inner = rcongr(d, inner_plus_b2j, swapped_inner, eq_swap_inner, &|d, t| {
        radd(d, wn, t)
    });
    let wn_swapped = radd(d, wn, swapped_inner);

    // `div1j + bound2j = natDivSucc (1+2) j`, DEFEQ to `bound3j`. Lift that
    // equation through BOTH the `_ + div1n` and the outer `wn + _` wrapping
    // in one congruence, since `swapped_inner = (div1j+bound2j)+div1n`.
    let div1j_plus_b2j = radd(d, div1j, bound2j);
    let nda = d.lemma(rat.nat_div_succ_add, &[one_nat, two_nat, j]);
    // : Eq div1j_plus_b2j (natDivSucc (Nat.add 1 2) j)  ~defeq~  bound3j
    let bound3j_div1n = radd(d, bound3j, div1n);
    let x2 = radd(d, wn, bound3j_div1n);
    let cong_bound3j = rcongr(d, div1j_plus_b2j, bound3j, nda, &|d, t| {
        let inner_t = radd(d, t, div1n);
        radd(d, wn, inner_t)
    });
    // : Eq wn_swapped x2

    let (_, eq_regroup) = rchain(
        d,
        big_rhs,
        &[
            (wn_inner_b2j, assoc_wn),
            (wn_swapped, cong_inner),
            (x2, cong_bound3j),
        ],
    );
    let q_le_x2 = rat_eq_rewrite(d, big_rhs, x2, eq_regroup, q_le_big, &|d, t| {
        rle(d, rat, q, t)
    });
    // : Rat.le q (radd wn (radd bound3j div1n))

    // Widen `div1n -> bound2n`.
    let bound2n = div_succ(d, p, 2, n);
    let mono_n = d.lemma(rat.nat_div_succ_le_add_left, &[one_nat, one_nat, n]);
    let refl_bound3j = d.lemma(rat.le_refl, &[bound3j]);
    let widen_n = d.lemma(
        rat.add_le_add,
        &[bound3j, bound3j, div1n, bound2n, refl_bound3j, mono_n],
    );
    let refl_wn = d.lemma(rat.le_refl, &[wn]);
    let inner_bound3j_div1n = radd(d, bound3j, div1n);
    let inner_bound3j_bound2n = radd(d, bound3j, bound2n);
    let step_widen = d.lemma(
        rat.add_le_add,
        &[
            wn,
            wn,
            inner_bound3j_div1n,
            inner_bound3j_bound2n,
            refl_wn,
            widen_n,
        ],
    );
    let x3 = radd(d, wn, inner_bound3j_bound2n);
    let q_le_x3 = d.lemma(rat.le_trans, &[q, x2, x3, q_le_x2, step_widen]);
    // : Rat.le q (radd wn (radd bound3j bound2n))

    // Reorder `wn+(bound3j+bound2n)` -> `bound3j+(wn+bound2n)`.
    let (z, eq_z) = radd3_swap_first(d, p, wn, bound3j, bound2n);
    let q_le_z = rat_eq_rewrite(d, x3, z, eq_z, q_le_x3, &|d, t| rle(d, rat, q, t));
    // : Rat.le q (radd bound3j (radd wn bound2n))

    let wn_bound2n = radd(d, wn, bound2n);
    let target2_le = d.lemma(rat.sub_le_of_le, &[q, bound3j, wn_bound2n, q_le_z]);
    // : Rat.le (rsub q bound3j) wn_bound2n  =  Rat.le target2 (radd wn bound2n)
    let at_n = d.lemma(rat.sub_le_of_le, &[target2, wn, bound2n, target2_le]);
    // : Rat.le (rsub target2 wn) bound2n

    let embedded_target2 = embed(d, p, target2);
    let cle_stmt = cle(d, p, embedded_target2, w);
    let ty = {
        let with_hyp = d.arrow(hzw_ty, cle_stmt);
        let with_k = d.pi_fv(k_fv, nat_ty, with_hyp);
        d.pi_fv(w_fv, carrier, with_k)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat_ty, at_n);
        let with_hzw = d.lam_fv(hzw_fv, hzw_ty, with_n);
        let with_k = d.lam_fv(k_fv, nat_ty, with_hzw);
        d.lam_fv(w_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bucket_clamp_lower,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the uniform bucket-index bound -----------------------------------------
//
// `bucket_index`'s own doc comment names this exactly: a COMPUTABLE `Nat`
// bound on `bucketIndex w k` for every `w` known only to satisfy `w <= bnd`
// (no lower bound on `w` at all -- unlike `bucket_clamp_lower`, which needs
// `0 <= w` to relate the clamp back DOWNWARD; bounding the clamp from ABOVE
// needs no sign hypothesis, since clamping only ever shrinks a large
// negative sample toward zero).

/// `CReal.bound x`. Local copy of `product.rs`'s private `bound_of` (see
/// that file's own copy for why this one line is duplicated rather than
/// shared across a module boundary).
fn ubound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.bound, &[x])
}

/// `CReal.bound x + 1` -- local copy of `product.rs`'s private
/// `magnitude_of`.
fn magnitude_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let base = ubound_of(d, p, x);
    d.succ(base)
}

/// `(CReal.bound x + 1)/1` -- local copy of `product.rs`'s private
/// `bound_value`, i.e. exactly the target [`CRealPrelude::bound_within`]
/// proves `seq x m` lands within.
fn bound_value(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let k = magnitude_of(d, p, x);
    let zero_nat = d.num(0);
    div_succ_at(d, p, k, zero_nat)
}

/// Admit [`CRealPrelude::bucket_index_bound`]. See that field's own doc
/// comment for the statement and the route: bound the clamped sample `q`
/// directly from `hle : CReal.le w bnd` and [`CRealPrelude::bound_within`]
/// (no regularity chain on `w` itself, unlike [`declare_bucket_clamp_upper`]/
/// [`declare_bucket_clamp_lower`]), then invert
/// [`CRealPrelude::bucket_index_floor_lower`]'s cross-multiplication in the
/// other direction.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_bucket_index_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let bnd_fv = d.fresh_fvar();
    let bnd = d.kernel().fvar(bnd_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    // --- shared setup, rebuilt identically to `bucket_index`'s own recipe --
    let (j, wj, q) = clamp_setup(d, p, w, k);
    let bj = sample(d, p, bnd, j);
    let zero_rat = rzero(d, rat);
    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let k1 = d.succ(k);
    let hle_ty = cle(d, p, w, bnd);

    // --- seq w j <= seq bnd j + 2/(j+1), from `hle` at index j -------------
    let bound2j = div_succ(d, p, 2, j);
    let hle_at_j = d.apply(hle, &[j]);
    let wj_le_bj_plus_b2j = d.lemma(rat.le_of_sub_le, &[wj, bj, bound2j, hle_at_j]);

    // --- seq bnd j <= B := (bound bnd + 1)/1, from `bound_within` ----------
    let bw = d.lemma(p.bound_within, &[bnd, j]);
    let b_val = bound_value(d, p, bnd);
    let (_, bj_le_b) = halves(d, p, bj, b_val, bw);

    // --- combine -> wj <= B + bound2j ---------------------------------------
    let refl_b2j = d.lemma(rat.le_refl, &[bound2j]);
    let widen1 = d.lemma(
        rat.add_le_add,
        &[bj, b_val, bound2j, bound2j, bj_le_b, refl_b2j],
    );
    let bj_plus_b2j = radd(d, bj, bound2j);
    let b_plus_b2j = radd(d, b_val, bound2j);
    let wj_le_b_plus_b2j = d.lemma(
        rat.le_trans,
        &[wj, bj_plus_b2j, b_plus_b2j, wj_le_bj_plus_b2j, widen1],
    );

    // --- widen 2/(j+1) up to natDivSucc 2 0 (= 2 as a Rat) ------------------
    let div1j = div_succ(d, p, 1, j);
    let div10 = div_succ(d, p, 1, zero_nat);
    let one_le_j = d.lemma(rat.nat_div_succ_le_one, &[j]);
    let doubled_le = d.lemma(
        rat.add_le_add,
        &[div1j, div10, div1j, div10, one_le_j, one_le_j],
    );
    let fuse_j = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, j]);
    let fuse_0 = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, zero_nat]);
    let div1j_double = radd(d, div1j, div1j);
    let div10_double = radd(d, div10, div10);
    let two_0 = div_succ(d, p, 2, zero_nat);
    let step_l = rat_eq_rewrite(d, div1j_double, bound2j, fuse_j, doubled_le, &|d, t| {
        rle(d, rat, t, div10_double)
    });
    let bound2j_le_20 = rat_eq_rewrite(d, div10_double, two_0, fuse_0, step_l, &|d, t| {
        rle(d, rat, bound2j, t)
    });

    // --- widen again -> wj <= B + two_0 -------------------------------------
    let refl_b = d.lemma(rat.le_refl, &[b_val]);
    let widen2 = d.lemma(
        rat.add_le_add,
        &[b_val, b_val, bound2j, two_0, refl_b, bound2j_le_20],
    );
    let b_plus_20 = radd(d, b_val, two_0);
    let wj_le_b_plus_20 = d.lemma(
        rat.le_trans,
        &[wj, b_plus_b2j, b_plus_20, wj_le_b_plus_b2j, widen2],
    );

    // --- fuse B + two_0 into one natDivSucc: C := magnitude_of(bnd) + 2 ----
    let magnitude_bnd = magnitude_of(d, p, bnd);
    let c_nat = NatOps::add(d, magnitude_bnd, two_nat);
    let fuse_c = d.lemma(rat.nat_div_succ_add, &[magnitude_bnd, two_nat, zero_nat]);
    let c_named = div_succ_at(d, p, c_nat, zero_nat);
    let wj_le_c = rat_eq_rewrite(d, b_plus_20, c_named, fuse_c, wj_le_b_plus_20, &|d, t| {
        rle(d, rat, wj, t)
    });

    // --- q <= c_named, via `Rat.max_le` -------------------------------------
    let zero_le_c = d.lemma(rat.zero_le_nat_div_succ, &[c_nat, zero_nat]);
    let q_le_c = d.lemma(rat.max_le, &[wj, zero_rat, c_named, wj_le_c, zero_le_c]);

    // --- chain with `bucket_index_floor_lower` ------------------------------
    let m_named = d.const_app(p.bucket_index, &[w, k]);
    let floor_lower = d.lemma(p.bucket_index_floor_lower, &[w, k]);
    let rep_m_named = div_succ_at(d, p, m_named, k);
    let m_le_c = d.lemma(
        rat.le_trans,
        &[rep_m_named, q, c_named, floor_lower, q_le_c],
    );
    // : Rat.le rep_m_named c_named

    // --- invert the cross-multiplication into a `Nat.le` --------------------
    //
    // `rep_m_named`/`c_named` unfold (Regular reducibility, `nat_div_succ`'s
    // own definition) to `Rat.normalize` applied to exactly the arguments
    // rebuilt below, so `rep_m`/`rep_c` are DEFEQ to them (Prop proof
    // irrelevance handles the positivity witnesses) -- the same bridge
    // `declare_bucket_index_floor`'s own `rep_m_named`/`rep_m` split relies
    // on.
    let mz = d.of_nat(m_named);
    let k1z = d.of_nat(k1);
    let pos_k1 = one_le_succ(d, k);
    let rep_m = normalize(d, mz, k1, pos_k1);
    let nm = num(d, rep_m);
    let dm = den(d, rep_m);
    let dm_z = den_z(d, rep_m);
    let dm_pos = den_pos(d, rep_m);
    let cross_m = d.lemma(rat.normalize_cross, &[mz, k1, pos_k1]);
    // : Eq (nm*k1z) (mz*dm_z)

    let cz = d.of_nat(c_nat);
    let one_lit = d.succ(zero_nat);
    let pos_one = one_le_succ(d, zero_nat);
    let rep_c = normalize(d, cz, one_lit, pos_one);
    let nc = num(d, rep_c);
    let dc = den(d, rep_c);
    let dc_z = den_z(d, rep_c);
    let dc_pos = den_pos(d, rep_c);
    let cross_c = d.lemma(rat.normalize_cross, &[cz, one_lit, pos_one]);
    // : Eq (nc*one_litz) (cz*dc_z)
    let one_litz = d.of_nat(one_lit);

    // `m_le_c`, DEFEQ-viewed at the `Int` level (`Rat.le q r := Int.le
    // (num q * den_z r) (num r * den_z q)`): `Int.le (nm*dc_z) (nc*dm_z)`.
    let nm_dcz = d.imul(nm, dc_z);
    let nc_dmz = d.imul(nc, dm_z);

    // Multiply both sides by `one_lit` (nonneg, no positivity needed) so the
    // `nc*one_litz` shape `cross_c` speaks about appears on the right.
    let h1 = d.lemma(rat.int_mul_le_mul_right, &[nm_dcz, nc_dmz, one_lit, m_le_c]);
    let lhs0 = d.imul(nm_dcz, one_litz);
    let rhs0 = d.imul(nc_dmz, one_litz);
    // h1 : Int.le lhs0 rhs0

    // LHS: (nm*dc_z)*one_litz = nm*(dc_z*one_litz) = nm*dc_z.
    let dcz_onelitz = d.imul(dc_z, one_litz);
    let assoc_l1 = d.lemma(rat.int.mul_assoc, &[nm, dc_z, one_litz]);
    let nm_dczonelitz = d.imul(nm, dcz_onelitz);
    let mul_one_dcz = d.lemma(rat.int.mul_one, &[dc_z]);
    let step_l2 = d.icongr(dcz_onelitz, dc_z, mul_one_dcz, &|d, t| d.imul(nm, t));
    let (lhs_target, eq_lhs) = d.ichain(lhs0, &[(nm_dczonelitz, assoc_l1), (nm_dcz, step_l2)]);

    // RHS: (nc*dm_z)*one_litz = nc*(dm_z*one_litz) = nc*(one_litz*dm_z)
    //    = (nc*one_litz)*dm_z = (cz*dc_z)*dm_z = cz*(dc_z*dm_z)
    //    = cz*(dm_z*dc_z) = (cz*dm_z)*dc_z.
    let dmz_onelitz = d.imul(dm_z, one_litz);
    let assoc_r1 = d.lemma(rat.int.mul_assoc, &[nc, dm_z, one_litz]);
    let nc_dmzonelitz = d.imul(nc, dmz_onelitz);
    let onelitz_dmz = d.imul(one_litz, dm_z);
    let comm_r2 = d.lemma(rat.int.mul_comm, &[dm_z, one_litz]);
    let step_r2 = d.icongr(dmz_onelitz, onelitz_dmz, comm_r2, &|d, t| d.imul(nc, t));
    let nc_onelitzdmz = d.imul(nc, onelitz_dmz);
    let nc_onelitz = d.imul(nc, one_litz);
    let nc_onelitz_dmz = d.imul(nc_onelitz, dm_z);
    let assoc_r3 = d.lemma(rat.int.mul_assoc, &[nc, one_litz, dm_z]);
    let step_r3 = d.isymm(nc_onelitz_dmz, nc_onelitzdmz, assoc_r3);
    let cz_dcz = d.imul(cz, dc_z);
    let cz_dcz_dmz = d.imul(cz_dcz, dm_z);
    let step_r4 = d.icongr(nc_onelitz, cz_dcz, cross_c, &|d, t| d.imul(t, dm_z));
    let dcz_dmz = d.imul(dc_z, dm_z);
    let cz_dczdmz = d.imul(cz, dcz_dmz);
    let assoc_r5 = d.lemma(rat.int.mul_assoc, &[cz, dc_z, dm_z]);
    let dmz_dcz = d.imul(dm_z, dc_z);
    let cz_dmzdcz = d.imul(cz, dmz_dcz);
    let comm_r6 = d.lemma(rat.int.mul_comm, &[dc_z, dm_z]);
    let step_r6 = d.icongr(dcz_dmz, dmz_dcz, comm_r6, &|d, t| d.imul(cz, t));
    let cz_dmz = d.imul(cz, dm_z);
    let cz_dmz_dcz = d.imul(cz_dmz, dc_z);
    let assoc_r7 = d.lemma(rat.int.mul_assoc, &[cz, dm_z, dc_z]);
    let step_r7 = d.isymm(cz_dmz_dcz, cz_dmzdcz, assoc_r7);

    let (rhs_target, eq_rhs) = d.ichain(
        rhs0,
        &[
            (nc_dmzonelitz, assoc_r1),
            (nc_onelitzdmz, step_r2),
            (nc_onelitz_dmz, step_r3),
            (cz_dcz_dmz, step_r4),
            (cz_dczdmz, assoc_r5),
            (cz_dmzdcz, step_r6),
            (cz_dmz_dcz, step_r7),
        ],
    );

    let motive1 = d.ieq_motive(lhs0, &|d, x| d.ile(x, rhs0));
    let step1 = d.itransport(lhs0, motive1, h1, lhs_target, eq_lhs);
    let motive2 = d.ieq_motive(rhs0, &|d, x| d.ile(lhs_target, x));
    let step2 = d.itransport(rhs0, motive2, step1, rhs_target, eq_rhs);
    // step2 : Int.le nm_dcz cz_dmz_dcz

    let h2 = d.lemma(
        rat.int_le_of_mul_le_mul_right,
        &[nm, cz_dmz, dc, dc_pos, step2],
    );
    // h2 : Int.le nm cz_dmz

    let h2k = d.lemma(rat.int_mul_le_mul_right, &[nm, cz_dmz, k1, h2]);
    let lhs2_0 = d.imul(nm, k1z);
    let rhs2_0 = d.imul(cz_dmz, k1z);
    // h2k : Int.le lhs2_0 rhs2_0

    // LHS: nm*k1z = mz*dm_z, directly `cross_m`.
    let lhs2_target = d.imul(mz, dm_z);

    // RHS: (cz*dm_z)*k1z = cz*(dm_z*k1z) = cz*(k1z*dm_z) = (cz*k1z)*dm_z.
    let dmz_k1z = d.imul(dm_z, k1z);
    let assoc_s1 = d.lemma(rat.int.mul_assoc, &[cz, dm_z, k1z]);
    let cz_dmzk1z = d.imul(cz, dmz_k1z);
    let k1z_dmz = d.imul(k1z, dm_z);
    let comm_s2 = d.lemma(rat.int.mul_comm, &[dm_z, k1z]);
    let step_s2 = d.icongr(dmz_k1z, k1z_dmz, comm_s2, &|d, t| d.imul(cz, t));
    let cz_k1zdmz = d.imul(cz, k1z_dmz);
    let cz_k1z = d.imul(cz, k1z);
    let cz_k1z_dmz = d.imul(cz_k1z, dm_z);
    let assoc_s3 = d.lemma(rat.int.mul_assoc, &[cz, k1z, dm_z]);
    let step_s3 = d.isymm(cz_k1z_dmz, cz_k1zdmz, assoc_s3);

    let (rhs2_target, eq_rhs2) = d.ichain(
        rhs2_0,
        &[
            (cz_dmzk1z, assoc_s1),
            (cz_k1zdmz, step_s2),
            (cz_k1z_dmz, step_s3),
        ],
    );

    let motive3 = d.ieq_motive(lhs2_0, &|d, x| d.ile(x, rhs2_0));
    let step3 = d.itransport(lhs2_0, motive3, h2k, lhs2_target, cross_m);
    let motive4 = d.ieq_motive(rhs2_0, &|d, x| d.ile(lhs2_target, x));
    let step4 = d.itransport(rhs2_0, motive4, step3, rhs2_target, eq_rhs2);
    // step4 : Int.le (mz*dm_z) (cz_k1z*dm_z)

    let h3 = d.lemma(
        rat.int_le_of_mul_le_mul_right,
        &[mz, cz_k1z, dm, dm_pos, step4],
    );
    // h3 : Int.le mz cz_k1z  ~defeq~ Nat.le m_named (Nat.mul c_nat k1)

    let m_bound = NatOps::mul(d, c_nat, k1);
    let conclusion = NatOps::le(d, m_named, m_bound);
    let ty = {
        let with_hyp = d.arrow(hle_ty, conclusion);
        let with_k = d.pi_fv(k_fv, nat_ty, with_hyp);
        let with_bnd = d.pi_fv(bnd_fv, carrier, with_k);
        d.pi_fv(w_fv, carrier, with_bnd)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, h3);
        let with_k = d.lam_fv(k_fv, nat_ty, with_hle);
        let with_bnd = d.lam_fv(bnd_fv, carrier, with_k);
        d.lam_fv(w_fv, carrier, with_bnd)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bucket_index_bound,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the general self-approximation lemmas ----------------------------------
//
// `bounded_of_uniformly_continuous`'s covering argument (module documentation)
// needs to bound its RATIONAL clamp `cap := max (seq bnd j - 1/(j+1)) 0` by
// `bnd` itself -- and that needs, for `bnd` specifically, the fact that `bnd`
// never falls below its own `j`-th sample by more than `1/(j+1)`. That is a
// property of every `CReal`, not of `bnd` in particular, and searching the
// prelude for it (`prelude_theorem_inventory --include-constructed`) turned up
// nothing: `CReal.bound_within` bounds a real by a FIXED integer constant, and
// `CReal.regular` bounds two SAMPLES of the same real against each other, but
// nothing bounds a real against one of ITS OWN samples directly. These two
// lemmas are exactly that, in both directions.

/// Admit [`CRealPrelude::sample_upper_bound`]. See that field's own doc
/// comment for the statement.
///
/// **Thin alias**, not an independent proof: this is the identical
/// proposition (up to the bound-variable name `m` vs. `n`) as
/// [`CRealPrelude::rat_approx_upper`]
/// (`crate::creal::density::declare_rat_approx_upper`), which was proved
/// four days earlier by a genuinely separate `k`-indexed regularity
/// argument. `shape_search --duplicates` (ADR-0608) flagged the pair, and
/// adjudication confirmed same statement + independent proofs — see
/// `docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`
/// groups 4/5. This forwards to `rat_approx_upper` instead of re-deriving,
/// matching the alias pattern already used elsewhere in this kernel
/// (`characterization.rs`, `weak_law_of_large_numbers`,
/// `nat_prelude/order_extra.rs::succ_le_succ`).
///
/// `rat_approx_upper` is the one kept canonical here, not `sample_upper_bound`
/// itself, purely because of *build order*: `density::declare_density` runs
/// before `uniform_continuity::declare_uniform_continuity` in
/// [`super::CRealPrelude`]'s build sequence, so `rat_approx_upper` is already
/// admitted by the time this runs and can be forwarded to; the reverse
/// direction would reference a name the kernel has not admitted yet.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sample_upper_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let wm = sample(d, p, x, m);
    let div1m = div_succ(d, p, 1, m);
    let target_q = radd(d, wm, div1m);
    let embedded_target = embed(d, p, target_q);
    let cle_stmt = cle(d, p, x, embedded_target);

    let ty = {
        let with_m = d.pi_fv(m_fv, nat_ty, cle_stmt);
        d.pi_fv(x_fv, carrier, with_m)
    };
    let value = {
        let forward = d.lemma(p.rat_approx_upper, &[x, m]);
        let with_m = d.lam_fv(m_fv, nat_ty, forward);
        d.lam_fv(x_fv, carrier, with_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sample_upper_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`CRealPrelude::sample_lower_bound`]. See that field's own doc
/// comment for the statement, and [`declare_sample_upper_bound`]'s for why
/// this is a thin alias rather than an independent derivation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sample_lower_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let wm = sample(d, p, x, m);
    let div1m = div_succ(d, p, 1, m);
    let target_q = rsub(d, rat, wm, div1m);
    let embedded_target = embed(d, p, target_q);
    let cle_stmt = cle(d, p, embedded_target, x);

    let ty = {
        let with_m = d.pi_fv(m_fv, nat_ty, cle_stmt);
        d.pi_fv(x_fv, carrier, with_m)
    };
    let value = {
        let forward = d.lemma(p.rat_approx_lower, &[x, m]);
        let with_m = d.lam_fv(m_fv, nat_ty, forward);
        d.lam_fv(x_fv, carrier, with_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sample_lower_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// The `BoundedOn`-hypothesis closure lemmas (`mul`, `sq`) and a concrete
/// instantiation, split into a SECOND entry point because they consume
/// `CReal.BoundedOn` and `CReal.abs_mul_le_of_bounds`
/// (`creal/derivative.rs`), which are not declared until
/// `derivative::declare_derivative` runs -- AFTER this module's own
/// [`declare_uniform_continuity`] in `creal.rs`'s build order. That order
/// cannot simply flip: `derivative.rs` itself calls `CReal.uniformly_continuous_id`
/// as a VALUE (three call sites), so it needs THIS module's early half
/// declared first. Wired in `creal.rs` right after
/// `derivative::declare_derivative`, the same split
/// `derivative::declare_has_derivative_pow_two`/`_pow` already use to wait
/// for `power::declare_power`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_uniform_continuity_products(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_uniformly_continuous_mul(d, p)?;
    declare_uniformly_continuous_sq(d, p)?;
    declare_bounded_on_id_unit(d, p)?;
    declare_uniformly_continuous_poly_example(d, p)
}

// --- shared term builders ----------------------------------------------------

/// `CReal → CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `Nat → Nat`.
fn nat_fn_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `Rat.natDivSucc k j`, with a **symbolic** `Nat` numerator `k`.
fn div_succ_at(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `Rat.natDivSucc k j`, with a literal numerator `k`.
fn div_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    div_succ_at(d, p, numerator, j)
}

/// `CReal.UniformlyContinuousOn F a b`.
fn uc_ty(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.uniformly_continuous_on, &[f, a, b])
}

/// `CReal.le (CReal.abs (CReal.add x (CReal.neg y))) (CReal.ofRat q)` —
/// `|x − y| ≤ q`, real-valued and index-free in `x, y`.
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = d.const_app(p.neg, &[y]);
    let diff = d.const_app(p.add, &[x, ny]);
    let magnitude = d.const_app(p.abs, &[diff]);
    let target = d.const_app(p.of_rat, &[q]);
    d.const_app(p.le, &[magnitude, target])
}

/// `∀ (n : Nat) (x y : CReal), le a x → le x b → le a y → le y b →
///   close_within x y (natDivSucc 1 (modulus n)) →
///   close_within (f x) (f y) (natDivSucc 1 n)`.
fn uc_spec_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    modulus: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let range_ax = d.const_app(p.le, &[a, x]);
    let range_xb = d.const_app(p.le, &[x, b]);
    let range_ay = d.const_app(p.le, &[a, y]);
    let range_yb = d.const_app(p.le, &[y, b]);

    let mod_n = d.apply(modulus, &[n]);
    let in_bound = div_succ(d, p, 1, mod_n);
    let hyp = close_within(d, p, x, y, in_bound);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let out_bound = div_succ(d, p, 1, n);
    let conclusion = close_within(d, p, fx, fy, out_bound);

    let body = d.arrow(hyp, conclusion);
    let with_yb = d.arrow(range_yb, body);
    let with_ay = d.arrow(range_ay, with_yb);
    let with_xb = d.arrow(range_xb, with_ay);
    let with_ax = d.arrow(range_ax, with_xb);
    let with_y = d.pi_fv(y_fv, carrier, with_ax);
    let with_x = d.pi_fv(x_fv, carrier, with_y);
    d.pi_fv(n_fv, nat, with_x)
}

// --- the carrier --------------------------------------------------------------

/// `CReal.UniformlyContinuousOn (F : CReal → CReal) (a b : CReal) : Type :=
///   mk (modulus : Nat → Nat) (spec : …)`.
///
/// A one-constructor inductive with three leading parameters (`F, a, b`) —
/// genuinely parametric, unlike `CReal` itself — copying `CReal`'s own
/// carrier shape one level up: a `Type`-valued data field and a dependent
/// `Prop`-valued spec field over it. See the module documentation for why
/// the data field is unavoidable.
fn declare_carrier(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // ty := Π (F : CReal → CReal) (a b : CReal), Type 0.
    let ty = {
        let f_fv = d.fresh_fvar();
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let with_b = d.pi_fv(b_fv, carrier, type0);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, func_ty, with_a)
    };

    // mk_ty := Π (F a b) (modulus : Nat → Nat) (spec : uc_spec_body …),
    //   UniformlyContinuousOn F a b.
    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let mod_fv = d.fresh_fvar();
        let modulus = d.kernel().fvar(mod_fv);

        let spec_ty = uc_spec_body(d, p, f, a, b, modulus);
        let result = uc_ty(d, p, f, a, b);

        let with_spec = d.arrow(spec_ty, result);
        let with_mod = d.pi_fv(mod_fv, nat_fn, with_spec);
        let with_b = d.pi_fv(b_fv, carrier, with_mod);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, func_ty, with_a)
    };

    d.kernel()
        .add_inductive(p.uniformly_continuous_on, &[], 3, ty, &[(p.uc_mk, mk_ty)])
}

/// The two projections: the modulus (large elimination, into `Type 0`) and
/// its spec (into `Prop`, with the motive at a witness `u` reading `u`'s
/// *own* modulus — mirroring exactly how
/// [`CReal.regular`](super::CRealPrelude::regular) projects `CReal`'s own
/// `Prop` field in [`super::declare_projections`]).
fn declare_projections(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();

    // modulus : ∀ F a b, UniformlyContinuousOn F a b → Nat → Nat
    //   := fun F a b u => UniformlyContinuousOn.rec F a b (fun _ => Nat → Nat)
    //        (fun modulus _ => modulus) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_uc = uc_ty(d, p, f, a, b);

        let motive = d
            .kernel()
            .lam(anon, carrier_uc, nat_fn, BinderInfo::Default);
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = uc_spec_body(d, p, f, a, b, modulus);
            let inner = d.kernel().lam(anon, spec_ty, modulus, BinderInfo::Default);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.uc_rec, vec![one]);
        let body = d.apply(rec, &[f, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_uc, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            d.lam_fv(f_fv, func_ty, with_a)
        };
        let ty = {
            let with_u = d.arrow(carrier_uc, nat_fn);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            d.pi_fv(f_fv, func_ty, with_a)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.uc_modulus,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 40),
        })?;
    }

    // spec : ∀ F a b (u : UniformlyContinuousOn F a b),
    //   uc_spec_body F a b (UniformlyContinuousOn.modulus F a b u)
    //   := fun F a b u => UniformlyContinuousOn.rec F a b
    //        (fun w => uc_spec_body F a b (UniformlyContinuousOn.modulus F a b w))
    //        (fun modulus spec => spec) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_uc = uc_ty(d, p, f, a, b);

        let claim = |d: &mut IntDev<'_>, w: ExprId| {
            let mod_of_w = d.const_app(p.uc_modulus, &[f, a, b, w]);
            uc_spec_body(d, p, f, a, b, mod_of_w)
        };

        let motive = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let body = claim(d, w);
            d.lam_fv(w_fv, carrier_uc, body)
        };
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = uc_spec_body(d, p, f, a, b, modulus);
            let spec_fv = d.fresh_fvar();
            let spec_var = d.kernel().fvar(spec_fv);
            let inner = d.lam_fv(spec_fv, spec_ty, spec_var);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.uc_rec, vec![zero_level]);
        let body = d.apply(rec, &[f, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_uc, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            d.lam_fv(f_fv, func_ty, with_a)
        };
        let ty = {
            let inner = claim(d, u);
            let with_u = d.pi_fv(u_fv, carrier_uc, inner);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            d.pi_fv(f_fv, func_ty, with_a)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.uc_spec,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// --- sub-interval restriction --------------------------------------------------

/// Admit `CReal.uniformlyContinuousOn_restrict : ∀ F a b a' b',
/// UniformlyContinuousOn F a b → le a a' → le a' b' → le b' b →
/// UniformlyContinuousOn F a' b'`.
///
/// The SAME modulus works on a narrower interval: `UniformlyContinuousOn`'s
/// `spec` (`uc_spec_body`, this file's own module-top helper) only ever uses
/// its range hypotheses (`a ≤ x`, `x ≤ b`, `a ≤ y`, `y ≤ b`) to state the
/// closeness implication, and `a ≤ a' ≤ x` / `y ≤ b' ≤ b` compose to exactly
/// those via [`CRealPrelude::le_trans`] -- no new estimate, no modulus
/// change. Built directly against [`CRealPrelude::uc_mk`] rather than
/// through the recursor: the new `spec` is a `lam` wrapping the ORIGINAL
/// witness's own `spec` (via [`CRealPrelude::uc_spec`]) applied to the
/// composed range proofs, so `UniformlyContinuousOn`'s definition is never
/// unfolded.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// refused a proof, not that a script gave up.
pub(super) fn declare_uniformly_continuous_on_restrict(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let ap_fv = d.fresh_fvar();
    let ap = d.kernel().fvar(ap_fv);
    let bp_fv = d.fresh_fvar();
    let bp = d.kernel().fvar(bp_fv);

    let u_ty = uc_ty(d, p, f, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let h1_ty = cle(d, p, a, ap); // le a a'
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = cle(d, p, ap, bp); // le a' b' -- carried in the statement for
    // symmetry with the task's own hypothesis list; not needed by the proof
    // (the restriction only ever composes `a <= a' <= x` and `y <= b' <= b`).
    let h2_fv = d.fresh_fvar();
    let h3_ty = cle(d, p, bp, b); // le b' b
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let modulus_u = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let spec_u = d.const_app(p.uc_spec, &[f, a, b, u]);
    // spec_u : uc_spec_body f a b modulus_u, i.e. ∀ n x y, le a x -> le x b
    // -> le a y -> le y b -> close_within x y (natDivSucc 1 (modulus_u n))
    // -> close_within (f x) (f y) (natDivSucc 1 n).

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hax_ty = cle(d, p, ap, x); // le a' x
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxb_ty = cle(d, p, x, bp); // le x b'
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);
    let hay_ty = cle(d, p, ap, y); // le a' y
    let hay_fv = d.fresh_fvar();
    let hay = d.kernel().fvar(hay_fv);
    let hyb_ty = cle(d, p, y, bp); // le y b'
    let hyb_fv = d.fresh_fvar();
    let hyb = d.kernel().fvar(hyb_fv);

    // Compose the narrower range hypotheses back to the original ones.
    let le_a_x = d.lemma(p.le_trans, &[a, ap, x, h1, hax]); // le a x
    let le_x_b = d.lemma(p.le_trans, &[x, bp, b, hxb, h3]); // le x b
    let le_a_y = d.lemma(p.le_trans, &[a, ap, y, h1, hay]); // le a y
    let le_y_b = d.lemma(p.le_trans, &[y, bp, b, hyb, h3]); // le y b

    let mod_n = d.apply(modulus_u, &[n]);
    let in_bound = div_succ(d, p, 1, mod_n);
    let hyp_ty = close_within(d, p, x, y, in_bound);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let concl = d.apply(spec_u, &[n, x, y, le_a_x, le_x_b, le_a_y, le_y_b, hyp]);
    // concl : close_within (f x) (f y) (natDivSucc 1 n) -- the ORIGINAL
    // witness's own spec, reused verbatim.

    let new_spec_value = {
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, concl);
        let with_hyb = d.lam_fv(hyb_fv, hyb_ty, with_hyp);
        let with_hay = d.lam_fv(hay_fv, hay_ty, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, with_hay);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let result = d.const_app(p.uc_mk, &[f, ap, bp, modulus_u, new_spec_value]);
    let concl_ty = uc_ty(d, p, f, ap, bp);

    let ty = {
        let after_h3 = d.arrow(h3_ty, concl_ty);
        let after_h2 = d.arrow(h2_ty, after_h3);
        let after_h1 = d.arrow(h1_ty, after_h2);
        let after_u = d.pi_fv(u_fv, u_ty, after_h1);
        let over_bp = d.pi_fv(bp_fv, carrier, after_u);
        let over_ap = d.pi_fv(ap_fv, carrier, over_bp);
        let over_b = d.pi_fv(b_fv, carrier, over_ap);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, func_ty, over_a)
    };
    let value = {
        let with_h3 = d.lam_fv(h3_fv, h3_ty, result);
        let with_h2 = d.lam_fv(h2_fv, h2_ty, with_h3);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
        let with_u = d.lam_fv(u_fv, u_ty, with_h1);
        let over_bp = d.lam_fv(bp_fv, carrier, with_u);
        let over_ap = d.lam_fv(ap_fv, carrier, over_bp);
        let over_b = d.lam_fv(b_fv, carrier, over_ap);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, func_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_on_restrict,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `id` -------------------------------------------------------------

/// `CReal.uniformly_continuous_id : ∀ a b, UniformlyContinuousOn (fun r => r) a b`.
///
/// The cheapest witness: with `F := id`, `close_within (f x) (f y) q` is
/// `close_within x y q` verbatim (up to beta/η), so the hypothesis at
/// `modulus n := n` **is** the conclusion.
fn declare_uniformly_continuous_id(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let modulus = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, n)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);
        let mod_n = d.apply(modulus, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x, y, in_bound);

        let with_h = d.lam_fv(h_fv, hyp, h);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[identity, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let applied = uc_ty(d, p, identity, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_id,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `const` ----------------------------------------------------------

/// `CReal.uniformly_continuous_const : ∀ c a b, UniformlyContinuousOn (fun _ => c) a b`.
///
/// Any modulus works — `fun _ => 0` is used — because `add c (neg c)` is
/// `Equiv`-zero ([`CReal.add_neg`](super::CRealPrelude::add_neg)), so the
/// conclusion holds independently of the hypothesis. The bulk of this proof
/// is the one fact that *isn't* a direct consequence of `add_neg`: `neg
/// zero` itself has to be shown `≤` an arbitrary nonnegative rational bound,
/// via [`CReal.ofRat_neg`](super::CRealPrelude::of_rat_neg) and
/// `Rat.neg_zero`.
fn declare_uniformly_continuous_const(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let const_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, c)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let zero_nat = d.num(0);
        d.lam_fv(ignore_fv, nat, zero_nat)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    // The one-time rational fact: `Equiv (neg zero_r) zero_r`, `zero_r :=
    // ofRat Rat.zero`, via `ofRat_neg` at `Rat.zero` and `Rat.neg_zero`.
    let rzero_expr = crate::rat_prelude::ops::rzero(d, rat);
    let zero_r = d.const_app(p.of_rat, &[rzero_expr]);
    let neg_zero_r = d.const_app(p.neg, &[zero_r]);

    let of_rat_neg_at_zero = d.lemma(p.of_rat_neg, &[rzero_expr]);
    let neg_rzero_expr = crate::rat_prelude::ops::rneg(d, rzero_expr);
    let neg_zero_eq = d.lemma(rat.neg_zero, &[]);
    let neg_zero_equiv_zero = rat_eq_rewrite(
        d,
        neg_rzero_expr,
        rzero_expr,
        neg_zero_eq,
        of_rat_neg_at_zero,
        &|d, t| {
            let ofr_t = d.const_app(p.of_rat, &[t]);
            let negz = d.const_app(p.neg, &[zero_r]);
            super::equiv(d, p, negz, ofr_t)
        },
    );
    // neg_zero_equiv_zero : Equiv (neg zero_r) zero_r.
    let h_negzero_le_zero = d.lemma(p.le_of_equiv, &[neg_zero_r, zero_r, neg_zero_equiv_zero]);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let x_ref = d.kernel().fvar(x_fv);
        let y_ref = d.kernel().fvar(y_fv);
        let range_ax = d.const_app(p.le, &[a, x_ref]);
        let range_xb = d.const_app(p.le, &[x_ref, b]);
        let range_ay = d.const_app(p.le, &[a, y_ref]);
        let range_yb = d.const_app(p.le, &[y_ref, b]);

        let q = div_succ(d, p, 1, n);
        let mod_n = d.apply(modulus, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x_ref, y_ref, in_bound);

        let add_c_negc = {
            let nc = d.const_app(p.neg, &[c]);
            d.const_app(p.add, &[c, nc])
        };

        // Rat.le Rat.zero q, and the two `le` facts against `zero_r`.
        let one_nat = d.num(1);
        let rat_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);
        let ofr_q = d.const_app(p.of_rat, &[q]);
        let h_zero_le_q = d.lemma(p.of_rat_le, &[rzero_expr, q, rat_nonneg]);
        let h_negzero_le_q = d.lemma(
            p.le_trans,
            &[neg_zero_r, zero_r, ofr_q, h_negzero_le_zero, h_zero_le_q],
        );

        // `Equiv (add c (neg c)) zero_r`, from `add_neg` (relies on `CReal.zero`
        // being *defined* as `ofRat Rat.zero`, hence defeq to `zero_r`).
        let h1 = d.lemma(p.add_neg, &[c]);

        let h_upper = d.lemma(p.le_of_equiv, &[add_c_negc, zero_r, h1]);
        let h4 = d.lemma(
            p.le_trans,
            &[add_c_negc, zero_r, ofr_q, h_upper, h_zero_le_q],
        );

        let neg_add_c_negc = d.const_app(p.neg, &[add_c_negc]);
        let h1_neg = d.lemma(p.neg_congr, &[add_c_negc, zero_r, h1]);
        let h1_neg_symm = d.lemma(p.equiv_symm, &[neg_add_c_negc, neg_zero_r, h1_neg]);
        let refl_q = d.lemma(p.equiv_refl, &[ofr_q]);
        let h6 = d.lemma(
            p.le_congr,
            &[
                neg_zero_r,
                neg_add_c_negc,
                ofr_q,
                ofr_q,
                h1_neg_symm,
                refl_q,
                h_negzero_le_q,
            ],
        );

        let conclusion = d.lemma(p.abs_le, &[add_c_negc, ofr_q, h4, h6]);
        // `conclusion : close_within c c (natDivSucc 1 n)`, unused by the
        // hypothesis: `const`'s spec is constant in `h`.
        let h = d.kernel().fvar(h_fv);
        let _ = h;

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[const_fn, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(c_fv, carrier, with_a)
    };
    let ty = {
        let applied = uc_ty(d, p, const_fn, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(c_fv, carrier, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_const,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `add` (closure under `+`) -----------------------------------
//
// The combined modulus is `hasDerivative_add`'s own
// (`creal/derivative.rs::declare_has_derivative_add`): `mF(2n+1) +
// mG(2n+1)`, `Nat.add` rather than `Nat.max` (`nat_prelude` has no
// `Nat.max`), unblocked by `Rat.natDivSucc_antitone`
// (`crate::RatPrelude::nat_div_succ_antitone`) with
// `Nat.le_add_right`/`Nat.add_comm` giving both `<=` directions
// (`mF(2n+1) <= mF(2n+1)+mG(2n+1)` directly, `mG(2n+1) <=
// mG(2n+1)+mF(2n+1) = mF(2n+1)+mG(2n+1)` after one commutation). What
// differs from `hasDerivative_add` is the error term itself: there is no
// `F'`/`G'` telescope here, so combining `F`'s and `G`'s own bounds is
// exactly the two-term triangle inequality, `abs_add_le`, built as a THIRD
// local copy below (`ring_helpers.rs`'s own module doc explains why this
// specific fact is deliberately not shared even though `series.rs` and
// `derivative.rs` already carry one copy each: they discharge the same
// statement through different underlying `neg_add`/`neg_add_distrib`
// proofs, and unifying either without the other is picking a route for one
// call site over the other) plus [`add4_comm`], which IS shared via
// `ring_helpers.rs`.

/// `Equiv (neg (add a b)) (add (neg a) (neg b))` — additive inverse
/// distributes over `add`. A third local copy of `series.rs`'s private
/// `neg_add` (see the section doc above for why it is not shared).
fn neg_add(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let s = d.const_app(p.add, &[a, b]);
    let na = d.const_app(p.neg, &[a]);
    let nb = d.const_app(p.neg, &[b]);
    let t = d.const_app(p.add, &[na, nb]);
    let ns = d.const_app(p.neg, &[s]);

    // f_proof : Equiv (add s t) zero, via add4_comm + the two `add_neg`s.
    let f_proof = {
        let (target1, h4) = add4_comm(d, p, a, b, na, nb);
        let a_na = d.const_app(p.add, &[a, na]);
        let b_nb = d.const_app(p.add, &[b, nb]);
        let add_zz = d.const_app(p.add, &[zero_c, zero_c]);
        let h_a = d.lemma(p.add_neg, &[a]); // a_na ~ zero
        let h_b = d.lemma(p.add_neg, &[b]); // b_nb ~ zero
        let h5 = d.lemma(p.add_congr, &[a_na, zero_c, b_nb, zero_c, h_a, h_b]); // target1 ~ add_zz
        let h6 = d.lemma(p.add_zero, &[zero_c]); // add_zz ~ zero
        let start = d.const_app(p.add, &[s, t]);
        echain(d, p, start, &[(target1, h4), (add_zz, h5), (zero_c, h6)])
    };

    // neg s ~ add(neg s)(zero) ~ add(neg s)(add s t) ~ (add(neg s)s)+t ~ add zero t ~ t
    let step_a_target = d.const_app(p.add, &[ns, zero_c]);
    let step_a = {
        let h = d.lemma(p.add_zero, &[ns]); // step_a_target ~ ns
        d.lemma(p.equiv_symm, &[step_a_target, ns, h]) // ns ~ step_a_target
    };

    let st = d.const_app(p.add, &[s, t]);
    let step_b_target = d.const_app(p.add, &[ns, st]);
    let step_b = {
        let f_symm = d.lemma(p.equiv_symm, &[st, zero_c, f_proof]); // zero ~ add s t
        let refl_ns = d.lemma(p.equiv_refl, &[ns]);
        d.lemma(p.add_congr, &[ns, ns, zero_c, st, refl_ns, f_symm])
        // step_a_target ~ step_b_target
    };

    let ns_s = d.const_app(p.add, &[ns, s]);
    let step_c_target = d.const_app(p.add, &[ns_s, t]);
    let step_c = {
        let assoc = d.lemma(p.add_assoc, &[ns, s, t]); // step_c_target ~ step_b_target
        d.lemma(p.equiv_symm, &[step_c_target, step_b_target, assoc])
        // step_b_target ~ step_c_target
    };

    let step_d_target = d.const_app(p.add, &[zero_c, t]);
    let step_d = {
        let x = {
            let comm = d.lemma(p.add_comm, &[ns, s]); // ns_s ~ add s ns
            let s_ns = d.const_app(p.add, &[s, ns]);
            let negl = d.lemma(p.add_neg, &[s]); // add s ns ~ zero
            d.lemma(p.equiv_trans, &[ns_s, s_ns, zero_c, comm, negl])
        };
        // x : ns_s ~ zero
        let refl_t = d.lemma(p.equiv_refl, &[t]);
        d.lemma(p.add_congr, &[ns_s, zero_c, t, t, x, refl_t])
        // step_c_target ~ step_d_target
    };

    let t_zero = d.const_app(p.add, &[t, zero_c]);
    let step_e = {
        let comm = d.lemma(p.add_comm, &[zero_c, t]); // step_d_target ~ t_zero
        let collapse = d.lemma(p.add_zero, &[t]); // t_zero ~ t
        d.lemma(p.equiv_trans, &[step_d_target, t_zero, t, comm, collapse])
        // step_d_target ~ t
    };

    echain(
        d,
        p,
        ns,
        &[
            (step_a_target, step_a),
            (step_b_target, step_b),
            (step_c_target, step_c),
            (step_d_target, step_d),
            (t, step_e),
        ],
    )
}

/// Chain `Equiv start …` through `(next, step)` pairs. Local restatement of
/// the identical helper private to `series.rs`/`derivative.rs`/
/// `ring_helpers.rs` (`ring_helpers.rs`'s own module doc explains why
/// `cadd`/`cmul`/`echain`-shaped one-liners are deliberately not shared
/// further than they already are).
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `le (abs (add a b)) (add (abs a) (abs b))` — the two-term triangle
/// inequality. A third local copy of `series.rs`'s/`derivative.rs`'s
/// private `abs_add_le` (see the section doc above for why).
fn abs_add_le(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let s = d.const_app(p.add, &[a, b]);
    let abs_a = d.const_app(p.abs, &[a]);
    let abs_b = d.const_app(p.abs, &[b]);
    let bound = d.const_app(p.add, &[abs_a, abs_b]);

    // premise1 : le (add a b) (add (abs a) (abs b))
    let le_a = d.lemma(p.le_abs_self, &[a]);
    let le_b = d.lemma(p.le_abs_self, &[b]);
    let premise1 = d.lemma(p.add_le_add, &[a, abs_a, b, abs_b, le_a, le_b]);

    // premise2 : le (neg (add a b)) (add (abs a) (abs b))
    let na = d.const_app(p.neg, &[a]);
    let nb = d.const_app(p.neg, &[b]);
    let t = d.const_app(p.add, &[na, nb]);
    let ns = d.const_app(p.neg, &[s]);
    let na_eq = neg_add(d, p, a, b); // ns ~ t
    let step1 = d.lemma(p.le_of_equiv, &[ns, t, na_eq]); // le ns t
    let nle_a = d.lemma(p.neg_le_abs, &[a]); // le na abs_a
    let nle_b = d.lemma(p.neg_le_abs, &[b]); // le nb abs_b
    let step2 = d.lemma(p.add_le_add, &[na, abs_a, nb, abs_b, nle_a, nle_b]); // le t bound
    let premise2 = d.lemma(p.le_trans, &[ns, t, bound, step1, step2]);

    d.lemma(p.abs_le, &[s, bound, premise1, premise2])
}

/// `CReal.abs_add_le : ∀ a b, le (abs (add a b)) (add (abs a) (abs b))` — the
/// two-term triangle inequality, promoted to a public kernel declaration.
///
/// UPDATE (this slice): this used to be the first of `CReal.abs_add_le`'s
/// **four** file-private proofs to gain a public name, with `series.rs`,
/// `derivative.rs`, `uniform_continuity.rs` itself and `deriv_unique.rs` each
/// still carrying their own copy (see the section doc above and
/// `ring_helpers.rs`'s doc comment for why the underlying PROOF-TERM
/// BUILDERS were never merged — the two routes are not byte-identical, only
/// statement-identical). That reasoning is about merging private *builders*;
/// it says nothing against a caller just CITING this already-published
/// theorem instead of re-deriving the statement. `series.rs`, `derivative.rs`
/// and `deriv_unique.rs` now do exactly that (`d.lemma(p.abs_add_le, &[a,
/// b])`), and their own private copies are gone; this file's other two
/// internal call sites (`declare_uniformly_continuous_mul`,
/// `declare_uniform_continuity_sums`) do too. Only this declaration's own
/// proof term, below, still calls the private [`abs_add_le`] helper — it has
/// to, since it IS what makes `p.abs_add_le` a citable fact in the first
/// place. This file's dispatch (`declare_uniform_continuity`) is the
/// earliest of the four named above to run in
/// `creal.rs::build_creal_prelude_uncached`, so this declaration lives here
/// and is called immediately before it, ahead of every current and future
/// consumer.
pub(super) fn declare_abs_add_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let body = abs_add_le(d, p, a, b);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let s = d.const_app(p.add, &[a, b]);
        let abs_s = d.const_app(p.abs, &[s]);
        let abs_a = d.const_app(p.abs, &[a]);
        let abs_b = d.const_app(p.abs, &[b]);
        let bound = d.const_app(p.add, &[abs_a, abs_b]);
        let conclusion = d.const_app(p.le, &[abs_s, bound]);
        let with_b = d.pi_fv(b_fv, carrier, conclusion);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.abs_add_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.uniformly_continuous_add : ∀ F G a b, UniformlyContinuousOn F a b
/// → UniformlyContinuousOn G a b → UniformlyContinuousOn (fun r => add (F
/// r) (G r)) a b`.
///
/// The combined modulus at accuracy `n` is `mF(2n+1) + mG(2n+1)`. `F`'s and
/// `G`'s own specs at `2n+1` each bound their own error by `1/(2n+2)`; the
/// triangle inequality ([`abs_add_le`]) bounds the combined error by their
/// sum; and `Rat.natDivSucc_add` + `Rat.natDivSucc_halve` fuse the two
/// `1/(2n+2)` bounds into the single target `1/(n+1)` — see the section doc
/// above for the full argument.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_uniformly_continuous_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let huc_f_ty = uc_ty(d, p, f, a, b);
    let huc_f_fv = d.fresh_fvar();
    let huc_f = d.kernel().fvar(huc_f_fv);
    let huc_g_ty = uc_ty(d, p, g, a, b);
    let huc_g_fv = d.fresh_fvar();
    let huc_g = d.kernel().fvar(huc_g_fv);

    let sum_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let sum = d.const_app(p.add, &[fr, gr]);
        d.lam_fv(r_fv, carrier, sum)
    };

    let mf = d.const_app(p.uc_modulus, &[f, a, b, huc_f]);
    let mg = d.const_app(p.uc_modulus, &[g, a, b, huc_g]);

    // `modulus_add n := mF (2n+1) + mG (2n+1)`.
    let modulus_add = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let two_n = d.mul(two, n);
        let e_prime = d.succ(two_n);
        let mf_e = d.apply(mf, &[e_prime]);
        let mg_e = d.apply(mg, &[e_prime]);
        let sum = d.add(mf_e, mg_e);
        d.lam_fv(n_fv, nat, sum)
    };

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);
        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);

        // `e_prime := succ(2*n)` — Bishop's index shift, the accuracy `F`'s
        // and `G`'s own specs are consulted at.
        let two = d.num(2);
        let two_n = d.mul(two, n);
        let e_prime = d.succ(two_n);
        let mf_e = d.apply(mf, &[e_prime]);
        let mg_e = d.apply(mg, &[e_prime]);
        let combined = d.add(mf_e, mg_e);

        let mod_n = d.apply(modulus_add, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x, y, in_bound);
        let h = d.kernel().fvar(h_fv);

        // --- read the combined-modulus hypothesis back down to F's and
        // G's own, via `nat_div_succ_antitone` --------------------------
        let mg_plus_mf = d.add(mg_e, mf_e);
        let nat_p = p.rat.int.nat;
        let h_le_f = d.lemma(nat_p.le_add_right, &[mf_e, mg_e]); // Le mf_e combined
        let raw_g = d.lemma(nat_p.le_add_right, &[mg_e, mf_e]); // Le mg_e mg_plus_mf
        let comm_eq = d.lemma(nat_p.add_comm, &[mg_e, mf_e]); // Eq mg_plus_mf combined
        let h_le_g = nat_rewrite_prop(d, mg_plus_mf, combined, comm_eq, raw_g, &|d, t| {
            NatOps::le(d, mg_e, t)
        });

        let r_f = div_succ(d, p, 1, mf_e);
        let r_g = div_succ(d, p, 1, mg_e);
        let r_combined = div_succ(d, p, 1, combined);
        let rat_f = d.lemma(p.rat.nat_div_succ_antitone, &[mf_e, combined, h_le_f]); // Rat.le r_combined r_f
        let rat_g = d.lemma(p.rat.nat_div_succ_antitone, &[mg_e, combined, h_le_g]); // Rat.le r_combined r_g

        let ofr_combined = d.const_app(p.of_rat, &[r_combined]);
        let ofr_f = d.const_app(p.of_rat, &[r_f]);
        let ofr_g = d.const_app(p.of_rat, &[r_g]);
        let creal_f = d.lemma(p.of_rat_le, &[r_combined, r_f, rat_f]); // le ofr_combined ofr_f
        let creal_g = d.lemma(p.of_rat_le, &[r_combined, r_g, rat_g]); // le ofr_combined ofr_g

        let ny = d.const_app(p.neg, &[y]);
        let diff_xy = d.const_app(p.add, &[x, ny]);
        let abs_diff = d.const_app(p.abs, &[diff_xy]);
        let hyp_f = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_f, h, creal_f]);
        let hyp_g = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_g, h, creal_g]);

        // --- F's and G's own errors, at accuracy `e_prime` ---------------
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);

        let spec_f = d.const_app(p.uc_spec, &[f, a, b, huc_f]);
        let spec_g = d.const_app(p.uc_spec, &[g, a, b, huc_g]);
        let close_f = d.apply(spec_f, &[e_prime, x, y, hax, hxb, hay, hyb, hyp_f]);
        let close_g = d.apply(spec_g, &[e_prime, x, y, hax, hxb, hay, hyb, hyp_g]);
        // close_f : close_within (F x) (F y) (natDivSucc 1 e_prime)
        // close_g : close_within (G x) (G y) (natDivSucc 1 e_prime)

        let neg_fy = d.const_app(p.neg, &[fy]);
        let error_f = d.const_app(p.add, &[fx, neg_fy]);
        let neg_gy = d.const_app(p.neg, &[gy]);
        let error_g = d.const_app(p.add, &[gx, neg_gy]);
        let abs_error_f = d.const_app(p.abs, &[error_f]);
        let abs_error_g = d.const_app(p.abs, &[error_g]);

        let r_prime = div_succ(d, p, 1, e_prime);
        let q_prime = d.const_app(p.of_rat, &[r_prime]);
        // close_f/close_g literally ARE `le abs_error_f q_prime` /
        // `le abs_error_g q_prime` (`close_within` unfolds to exactly this).

        // --- combine via the triangle inequality --------------------------
        let (target, add4_proof) = add4_comm(d, p, fx, gx, neg_fy, neg_gy);
        // target = add error_f error_g;
        // add4_proof : Equiv (add(add fx gx)(add neg_fy neg_gy)) target
        let abs_target = d.const_app(p.abs, &[target]);
        // Consumes the public `CReal.abs_add_le` directly rather than this
        // file's own private `abs_add_le` helper (still used at the `mul`
        // call site below) — the first call site converted to the public
        // theorem.
        let triangle = d.lemma(p.abs_add_le, &[error_f, error_g]);
        // triangle : le abs_target (add abs_error_f abs_error_g)
        let sum_bounds = d.lemma(
            p.add_le_add,
            &[abs_error_f, q_prime, abs_error_g, q_prime, close_f, close_g],
        );
        let abs_ef_plus_eg = d.const_app(p.add, &[abs_error_f, abs_error_g]);
        let q_prime_plus_q_prime = d.const_app(p.add, &[q_prime, q_prime]);
        let combined_le = d.lemma(
            p.le_trans,
            &[
                abs_target,
                abs_ef_plus_eg,
                q_prime_plus_q_prime,
                triangle,
                sum_bounds,
            ],
        );
        // combined_le : le abs_target (add q_prime q_prime)

        // --- combined_diff ~ target, lifted through `abs` ------------------
        let fx_gx = d.const_app(p.add, &[fx, gx]);
        let fy_gy = d.const_app(p.add, &[fy, gy]);
        let neg_fy_gy = d.const_app(p.neg, &[fy_gy]);
        let combined_diff = d.const_app(p.add, &[fx_gx, neg_fy_gy]);
        let abs_combined_diff = d.const_app(p.abs, &[combined_diff]);

        let neg_fy_neg_gy = d.const_app(p.add, &[neg_fy, neg_gy]);
        let step1_target = d.const_app(p.add, &[fx_gx, neg_fy_neg_gy]);
        let neg_add_fy_gy = neg_add(d, p, fy, gy); // neg_fy_gy ~ neg_fy_neg_gy
        let refl_fx_gx = d.lemma(p.equiv_refl, &[fx_gx]);
        let step1 = d.lemma(
            p.add_congr,
            &[
                fx_gx,
                fx_gx,
                neg_fy_gy,
                neg_fy_neg_gy,
                refl_fx_gx,
                neg_add_fy_gy,
            ],
        );
        // step1 : combined_diff ~ step1_target

        let chain_ct = echain(
            d,
            p,
            combined_diff,
            &[(step1_target, step1), (target, add4_proof)],
        );
        // chain_ct : combined_diff ~ target
        let chain_tc = d.lemma(p.equiv_symm, &[combined_diff, target, chain_ct]);
        // chain_tc : target ~ combined_diff
        let abs_equiv = d.lemma(p.abs_congr, &[target, combined_diff, chain_tc]);
        // abs_equiv : abs_target ~ abs_combined_diff

        // --- fuse `add q_prime q_prime` down to `ofRat (natDivSucc 1 n)` --
        let one_nat = d.num(1);
        let of_rat_add_proof = d.lemma(p.of_rat_add, &[r_prime, r_prime]);
        // Equiv (add q_prime q_prime) (ofRat (Rat.add r_prime r_prime))
        let eq1 = d.lemma(p.rat.nat_div_succ_add, &[one_nat, one_nat, e_prime]);
        let two_e_prime = div_succ(d, p, 2, e_prime);
        let radd_r_prime_r_prime = radd(d, r_prime, r_prime);
        let step_a = rat_eq_rewrite(
            d,
            radd_r_prime_r_prime,
            two_e_prime,
            eq1,
            of_rat_add_proof,
            &|d, t| {
                let oft = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[q_prime_plus_q_prime, oft])
            },
        );
        // Equiv (add q_prime q_prime) (ofRat two_e_prime)
        let eq2 = d.lemma(p.rat.nat_div_succ_halve, &[n]);
        let out_bound_rat = div_succ(d, p, 1, n);
        let fuse_equiv = rat_eq_rewrite(d, two_e_prime, out_bound_rat, eq2, step_a, &|d, t| {
            let oft = d.const_app(p.of_rat, &[t]);
            d.const_app(p.equiv, &[q_prime_plus_q_prime, oft])
        });
        // fuse_equiv : Equiv (add q_prime q_prime) (ofRat out_bound_rat)
        let ofr_out_bound = d.const_app(p.of_rat, &[out_bound_rat]);

        let result = d.lemma(
            p.le_congr,
            &[
                abs_target,
                abs_combined_diff,
                q_prime_plus_q_prime,
                ofr_out_bound,
                abs_equiv,
                fuse_equiv,
                combined_le,
            ],
        );
        // result : close_within (sum_fn x) (sum_fn y) (natDivSucc 1 n)

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[sum_fn, a, b, modulus_add, spec]);
    let value = {
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, mk_applied);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_b = d.lam_fv(b_fv, carrier, with_huc_f);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let applied = uc_ty(d, p, sum_fn, a, b);
        let with_huc_g = d.arrow(huc_g_ty, applied);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_b = d.pi_fv(b_fv, carrier, with_huc_f);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_add,
        uparams: vec![],
        ty,
        value,
    })
}

// --- shared term builders, round two (local copies of small pieces from
// `creal/derivative.rs`, which are private to that file -- see the module
// doc's rationale for `echain`/`neg_add`/`abs_add_le`, which these join) ---

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// From `h : Equiv a b`, `Equiv b a`.
fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// `ofRat (natDivSucc (Nat.succ k) 0)` -- "`k+1`", `CReal.BoundedOn`'s own
/// magnitude bound. Local copy of `creal/derivative.rs::mag_bound` (private
/// there); constructed via the identical sequence of calls
/// (`d.succ`/`d.num`/[`div_succ_at`]/`p.of_rat`) so that, for the SAME `k`
/// expression, it interns to the SAME term `BoundedOn`'s own declaration
/// unfolds to -- which is what lets [`bounded_on_applied`]'s hypotheses be
/// used directly against it below.
fn mag_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let r = div_succ_at(d, p, succ_k, zero_idx);
    d.const_app(p.of_rat, &[r])
}

/// `le zero (mag_bound k)`, via `Rat.zero_le_natDivSucc` lifted by
/// `CReal.ofRat_le` -- `CReal.zero` is defeq to `ofRat Rat.zero` (the same
/// fact [`declare_uniformly_continuous_const`] already relies on).
fn mag_bound_nonneg(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let bound_rat = div_succ_at(d, p, succ_k, zero_idx);
    let rzero_expr = crate::rat_prelude::ops::rzero(d, p.rat);
    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[succ_k, zero_idx]);
    d.lemma(p.of_rat_le, &[rzero_expr, bound_rat, rat_nonneg])
}

/// `CReal.BoundedOn h a b k` applied.
fn bounded_on_applied(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    h: ExprId,
    a: ExprId,
    b: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.bounded_on, &[h, a, b, k])
}

/// `(k+1)*m + k` -- `Rat.natDivSucc_scale`'s own index shape. Local copy of
/// `creal/derivative.rs::rescale_index` (private there).
fn rescale_index(d: &mut IntDev<'_>, k: ExprId, m: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let mul_km = d.mul(succ_k, m);
    d.add(mul_km, k)
}

/// From `h_ab_zero : Equiv (add a b) zero`, `Equiv b (neg a)` -- `b` is the
/// unique additive inverse of `a`. Local copy of
/// `creal/derivative.rs::neg_unique` (private there).
fn neg_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h_ab_zero: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_a = cneg(d, p, a);

    let add_a_nega = cadd(d, p, a, neg_a);
    let add_nega_a = cadd(d, p, neg_a, a);
    let h_add_neg = d.lemma(p.add_neg, &[a]);
    let comm0 = d.lemma(p.add_comm, &[a, neg_a]);
    let symm_h = esymm(d, p, add_a_nega, zero_c, h_add_neg);
    let zero_equiv_nega_a = d.lemma(
        p.equiv_trans,
        &[zero_c, add_a_nega, add_nega_a, symm_h, comm0],
    );

    let add_b_zero = cadd(d, p, b, zero_c);
    let add_zero_b = cadd(d, p, zero_c, b);
    let h_addzero_b = d.lemma(p.add_zero, &[b]);
    let b_equiv_addbzero = esymm(d, p, add_b_zero, b, h_addzero_b);
    let comm_b0 = d.lemma(p.add_comm, &[b, zero_c]);
    let b_equiv_addzerob = d.lemma(
        p.equiv_trans,
        &[b, add_b_zero, add_zero_b, b_equiv_addbzero, comm_b0],
    );

    let addnega_a = cadd(d, p, neg_a, a);
    let addnega_a_plus_b = cadd(d, p, addnega_a, b);
    let refl_b = erefl(d, p, b);
    let subst1 = d.lemma(
        p.add_congr,
        &[zero_c, addnega_a, b, b, zero_equiv_nega_a, refl_b],
    );

    let a_plus_b = cadd(d, p, a, b);
    let nega_plus_aplusb = cadd(d, p, neg_a, a_plus_b);
    let assoc = d.lemma(p.add_assoc, &[neg_a, a, b]);

    let nega_plus_zero = cadd(d, p, neg_a, zero_c);
    let refl_nega = erefl(d, p, neg_a);
    let subst2 = d.lemma(
        p.add_congr,
        &[neg_a, neg_a, a_plus_b, zero_c, refl_nega, h_ab_zero],
    );

    let final_step = d.lemma(p.add_zero, &[neg_a]);

    echain(
        d,
        p,
        b,
        &[
            (add_zero_b, b_equiv_addzerob),
            (addnega_a_plus_b, subst1),
            (nega_plus_aplusb, assoc),
            (nega_plus_zero, subst2),
            (neg_a, final_step),
        ],
    )
}

/// `Equiv (add (neg x) x) zero`.
fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// `Equiv (neg (neg x)) x`.
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (mul x (neg y)) (neg (mul x y))`. Local copy of
/// `creal/derivative.rs::mul_neg_equiv` (private there) -- see this file's
/// module documentation, "Scalar multiplication", for why this identity was
/// previously flagged as an unwritten prerequisite.
fn mul_neg_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let xy = cmul(d, p, x, y);
    let x_ny = cmul(d, p, x, ny);
    let y_plus_ny = cadd(d, p, y, ny);
    let x_times_sum = cmul(d, p, x, y_plus_ny);

    let h_add_neg_y = d.lemma(p.add_neg, &[y]);
    let refl_x = erefl(d, p, x);
    let h_mulcongr = d.lemma(p.mul_congr, &[x, x, y_plus_ny, zero_c, refl_x, h_add_neg_y]);
    let x_zero = cmul(d, p, x, zero_c);
    let h_mulzero = d.lemma(p.mul_zero, &[x]);
    let sum_equiv_zero = echain(
        d,
        p,
        x_times_sum,
        &[(x_zero, h_mulcongr), (zero_c, h_mulzero)],
    );

    let h_ld = d.lemma(p.left_distrib, &[x, y, ny]);
    let sum_of_products = cadd(d, p, xy, x_ny);
    let symm_ld = esymm(d, p, x_times_sum, sum_of_products, h_ld);
    let h_sum_zero = d.lemma(
        p.equiv_trans,
        &[
            sum_of_products,
            x_times_sum,
            zero_c,
            symm_ld,
            sum_equiv_zero,
        ],
    );

    neg_unique(d, p, xy, x_ny, h_sum_zero)
}

/// From `h : le (abs w) q`, derive `le (abs (neg w)) q`. `creal/exp_fn.rs`
/// and `creal/trig_fn.rs` both had a copy of this same helper (the latter
/// out of scope here, a live lane); `exp_fn.rs` now imports this one
/// instead of keeping its own.
pub(super) fn abs_neg_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    w: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let abs_w = cabs(d, p, w);
    let neg_w = cneg(d, p, w);
    let w_le_absw = d.lemma(p.le_abs_self, &[w]);
    let w_le_q = d.lemma(p.le_trans, &[w, abs_w, q, w_le_absw, h]);
    let negw_le_absw = d.lemma(p.neg_le_abs, &[w]);
    let negw_le_q = d.lemma(p.le_trans, &[neg_w, abs_w, q, negw_le_absw, h]);

    let neg_neg_w = cneg(d, p, neg_w);
    let nn = double_neg(d, p, w); // Equiv neg_neg_w w
    let nn_symm = esymm(d, p, neg_neg_w, w, nn); // Equiv w neg_neg_w
    let refl_q = erefl(d, p, q);
    let nnw_le_q = d.lemma(p.le_congr, &[w, neg_neg_w, q, q, nn_symm, refl_q, w_le_q]);
    // nnw_le_q : le neg_neg_w q

    d.lemma(p.abs_le, &[neg_w, q, negw_le_q, nnw_le_q])
}

/// `Equiv (add (add x (neg z)) (add z w)) (add x w)` -- the four-term
/// telescoping cancellation the product rule's cross terms collapse
/// through, once each is expressed as `(A - P) + (P - B)`.
fn middle_cancel(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, z: ExprId, w: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, z);
    let x_nz = cadd(d, p, x, nz);
    let z_w = cadd(d, p, z, w);
    let lhs = cadd(d, p, x_nz, z_w);

    let nz_zw = cadd(d, p, nz, z_w);
    let x_plus_nzzw = cadd(d, p, x, nz_zw);
    let assoc1 = d.lemma(p.add_assoc, &[x, nz, z_w]);
    // assoc1 : Equiv lhs x_plus_nzzw

    let nz_z = cadd(d, p, nz, z);
    let z_nz = cadd(d, p, z, nz);
    let comm_nz_z = d.lemma(p.add_comm, &[nz, z]);
    let cancel_z = d.lemma(p.add_neg, &[z]);
    let nzz_zero = echain(d, p, nz_z, &[(z_nz, comm_nz_z), (zero_c, cancel_z)]);
    // nzz_zero : Equiv nz_z zero_c

    let refl_w = erefl(d, p, w);
    let nzzw_zerow = d.lemma(p.add_congr, &[nz_z, zero_c, w, w, nzz_zero, refl_w]);
    // nzzw_zerow : Equiv (add nz_z w) (add zero_c w)
    let nzz_w = cadd(d, p, nz_z, w);
    let zero_w = cadd(d, p, zero_c, w);

    let assoc2 = d.lemma(p.add_assoc, &[nz, z, w]);
    // assoc2 : Equiv nzz_w nz_zw
    let assoc2_symm = esymm(d, p, nzz_w, nz_zw, assoc2);
    // assoc2_symm : Equiv nz_zw nzz_w

    let w_zero = cadd(d, p, w, zero_c);
    let comm_0w = d.lemma(p.add_comm, &[zero_c, w]);
    let zerow_w = d.lemma(p.add_zero, &[w]);
    let zerow_chain = echain(d, p, zero_w, &[(w_zero, comm_0w), (w, zerow_w)]);
    // zerow_chain : Equiv zero_w w

    let nz_zw_to_w = echain(
        d,
        p,
        nz_zw,
        &[(nzz_w, assoc2_symm), (zero_w, nzzw_zerow), (w, zerow_chain)],
    );
    // nz_zw_to_w : Equiv nz_zw w

    let refl_x = erefl(d, p, x);
    let x_plus_result = d.lemma(p.add_congr, &[x, x, nz_zw, w, refl_x, nz_zw_to_w]);
    // x_plus_result : Equiv x_plus_nzzw (add x w)
    let x_w = cadd(d, p, x, w);

    echain(d, p, lhs, &[(x_plus_nzzw, assoc1), (x_w, x_plus_result)])
}

/// `Equiv (add term1 term2) (add (mul fx gx) (neg (mul fy gy)))`, where
/// `term1 := mul fx (add gx (neg gy))` and `term2 := mul gy (add fx (neg
/// fy))` -- `F(x)G(x) - F(y)G(y) = F(x)(G(x)-G(y)) + G(y)(F(x)-F(y))`, the
/// genuine product-of-bounds estimate this file's module documentation
/// flags (as opposed to a triangle inequality). Returns `(term1, term2,
/// target, proof)`.
fn product_diff_identity(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    fx: ExprId,
    fy: ExprId,
    gx: ExprId,
    gy: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let neg_gy = cneg(d, p, gy);
    let neg_fy = cneg(d, p, fy);
    let diff_g = cadd(d, p, gx, neg_gy);
    let diff_f = cadd(d, p, fx, neg_fy);
    let term1 = cmul(d, p, fx, diff_g);
    let term2 = cmul(d, p, gy, diff_f);

    let a_val = cmul(d, p, fx, gx); // A
    let p_val = cmul(d, p, fx, gy); // P
    let b_val = cmul(d, p, fy, gy); // B
    let neg_p_val = cneg(d, p, p_val);
    let neg_b_val = cneg(d, p, b_val);

    // term1 ~ add A (neg P)
    let ld1 = d.lemma(p.left_distrib, &[fx, gx, neg_gy]);
    // ld1 : Equiv term1 (add A (mul fx neg_gy))
    let mfx_ngy = cmul(d, p, fx, neg_gy);
    let mne1 = mul_neg_equiv(d, p, fx, gy); // Equiv mfx_ngy neg_p_val
    let refl_a = erefl(d, p, a_val);
    let cong1 = d.lemma(
        p.add_congr,
        &[a_val, a_val, mfx_ngy, neg_p_val, refl_a, mne1],
    );
    // cong1 : Equiv (add A mfx_ngy) (add A neg_p_val)
    let a_plus_mfxngy = cadd(d, p, a_val, mfx_ngy);
    let a_plus_negp = cadd(d, p, a_val, neg_p_val);
    let term1_equiv = echain(d, p, term1, &[(a_plus_mfxngy, ld1), (a_plus_negp, cong1)]);
    // term1_equiv : Equiv term1 a_plus_negp

    // term2 ~ add P (neg B)
    let ld2 = d.lemma(p.left_distrib, &[gy, fx, neg_fy]);
    // ld2 : Equiv term2 (add (mul gy fx) (mul gy neg_fy))
    let mgy_fx = cmul(d, p, gy, fx);
    let mgy_nfy = cmul(d, p, gy, neg_fy);
    let comm_gyfx = d.lemma(p.mul_comm, &[gy, fx]); // Equiv mgy_fx p_val
    let mgy_fy = cmul(d, p, gy, fy);
    let mne2 = mul_neg_equiv(d, p, gy, fy); // Equiv mgy_nfy (neg mgy_fy)
    let comm_gyfy = d.lemma(p.mul_comm, &[gy, fy]); // Equiv mgy_fy b_val
    let neg_mgyfy = cneg(d, p, mgy_fy);
    let neg_comm_gyfy = d.lemma(p.neg_congr, &[mgy_fy, b_val, comm_gyfy]);
    // neg_comm_gyfy : Equiv neg_mgyfy neg_b_val
    let mgy_nfy_to_negb = echain(
        d,
        p,
        mgy_nfy,
        &[(neg_mgyfy, mne2), (neg_b_val, neg_comm_gyfy)],
    );
    // mgy_nfy_to_negb : Equiv mgy_nfy neg_b_val
    let cong2 = d.lemma(
        p.add_congr,
        &[
            mgy_fx,
            p_val,
            mgy_nfy,
            neg_b_val,
            comm_gyfx,
            mgy_nfy_to_negb,
        ],
    );
    // cong2 : Equiv (add mgy_fx mgy_nfy) (add p_val neg_b_val)
    let mgyfx_plus_mgynfy = cadd(d, p, mgy_fx, mgy_nfy);
    let p_plus_negb = cadd(d, p, p_val, neg_b_val);
    let term2_equiv = echain(
        d,
        p,
        term2,
        &[(mgyfx_plus_mgynfy, ld2), (p_plus_negb, cong2)],
    );
    // term2_equiv : Equiv term2 p_plus_negb

    let sum_equiv = d.lemma(
        p.add_congr,
        &[
            term1,
            a_plus_negp,
            term2,
            p_plus_negb,
            term1_equiv,
            term2_equiv,
        ],
    );
    // sum_equiv : Equiv (add term1 term2) (add a_plus_negp p_plus_negb)
    let lhs_telescope = cadd(d, p, a_plus_negp, p_plus_negb);

    let telescope = middle_cancel(d, p, a_val, p_val, neg_b_val);
    // telescope : Equiv lhs_telescope (add a_val neg_b_val)
    let target = cadd(d, p, a_val, neg_b_val);

    let sum_term1_term2 = cadd(d, p, term1, term2);
    let proof = echain(
        d,
        p,
        sum_term1_term2,
        &[(lhs_telescope, sum_equiv), (target, telescope)],
    );

    (term1, term2, target, proof)
}

/// From `e_prime := rescale_index(k, m)`, `Equiv (mul (mag_bound k) (ofRat
/// (natDivSucc 1 e_prime))) (ofRat (natDivSucc 1 m))`. Local copy of
/// `creal/derivative.rs::fold_index0_first` (private there). Returns
/// `(big_expr, small_expr, ofr_out, proof)`.
fn fold_mag_bound_error(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    m: ExprId,
    e_prime: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let bound_rat = div_succ_at(d, p, succ_k, zero_idx); // natDivSucc (succ k) 0
    let big_expr = d.const_app(p.of_rat, &[bound_rat]);

    let r_prime = div_succ(d, p, 1, e_prime); // natDivSucc 1 e_prime
    let small_expr = d.const_app(p.of_rat, &[r_prime]);

    let one_nat = d.num(1);
    let mul_succk_1 = d.mul(succ_k, one_nat);
    let succ_k_e_prime = div_succ_at(d, p, succ_k, e_prime);
    let out_bound_rat = div_succ(d, p, 1, m);

    let eq_mul = d.lemma(p.rat.nat_div_succ_mul, &[succ_k, one_nat, e_prime]);
    let mul_one_eq = d.lemma(p.rat.int.nat.mul_one, &[succ_k]);
    let eq_fold = nat_eq_to_rat(d, mul_succk_1, succ_k, mul_one_eq, &|d, x| {
        div_succ_at(d, p, x, e_prime)
    });
    let eq_scale = d.lemma(p.rat.nat_div_succ_scale, &[k, m]);

    let of_rat_mul_proof = d.lemma(p.of_rat_mul, &[bound_rat, r_prime]);
    let mul_bb_ofre = cmul(d, p, big_expr, small_expr);
    let rat_prod = {
        let f_ap = d.int().rat_mul;
        d.const_app(f_ap, &[bound_rat, r_prime])
    };
    let mul_succk1_e_prime = div_succ_at(d, p, mul_succk_1, e_prime);

    let motive = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[mul_bb_ofre, oft])
    };
    let step_a = rat_eq_rewrite(
        d,
        rat_prod,
        mul_succk1_e_prime,
        eq_mul,
        of_rat_mul_proof,
        &motive,
    );
    let step_b = rat_eq_rewrite(
        d,
        mul_succk1_e_prime,
        succ_k_e_prime,
        eq_fold,
        step_a,
        &motive,
    );
    let step_c = rat_eq_rewrite(d, succ_k_e_prime, out_bound_rat, eq_scale, step_b, &motive);
    let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);

    (big_expr, small_expr, ofr_out, step_c)
}

// --- witness: `neg` (closure under unary negation) --------------------------

/// `CReal.uniformly_continuous_neg : ∀ F a b, UniformlyContinuousOn F a b ->
/// UniformlyContinuousOn (fun r => neg (F r)) a b`.
///
/// The modulus is UNCHANGED (`mF` itself) -- negating both sides of a
/// closeness bound does not weaken it, and [`abs_neg_le`] carries the bound
/// across `abs (neg _)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_uniformly_continuous_neg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let huc_ty = uc_ty(d, p, f, a, b);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);

    let neg_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let nfr = cneg(d, p, fr);
        d.lam_fv(r_fv, carrier, nfr)
    };

    let mf = d.const_app(p.uc_modulus, &[f, a, b, huc]);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);
        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);

        let mf_n = d.apply(mf, &[n]);
        let in_bound = div_succ(d, p, 1, mf_n);
        let hyp = close_within(d, p, x, y, in_bound);
        let h = d.kernel().fvar(h_fv);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let spec_f = d.const_app(p.uc_spec, &[f, a, b, huc]);
        let close_f = d.apply(spec_f, &[n, x, y, hax, hxb, hay, hyb, h]);

        let neg_fy = cneg(d, p, fy);
        let w = cadd(d, p, fx, neg_fy);
        let out_bound = div_succ(d, p, 1, n);
        let q = d.const_app(p.of_rat, &[out_bound]);
        // close_f : le (abs w) q

        let bound_neg_w = abs_neg_le(d, p, w, q, close_f);
        let neg_w = cneg(d, p, w);
        // bound_neg_w : le (abs neg_w) q

        let neg_fx = cneg(d, p, fx);
        let neg_neg_fy = cneg(d, p, neg_fy);
        let target = cadd(d, p, neg_fx, neg_neg_fy);
        let nadd = neg_add(d, p, fx, neg_fy);
        // nadd : Equiv neg_w target

        let abs_negw = cabs(d, p, neg_w);
        let abs_target = cabs(d, p, target);
        let abs_equiv = d.lemma(p.abs_congr, &[neg_w, target, nadd]);
        let refl_q = erefl(d, p, q);
        let result = d.lemma(
            p.le_congr,
            &[abs_negw, abs_target, q, q, abs_equiv, refl_q, bound_neg_w],
        );
        // result : le abs_target q

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[neg_fn, a, b, mf, spec]);
    let value = {
        let with_huc = d.lam_fv(huc_fv, huc_ty, mk_applied);
        let with_b = d.lam_fv(b_fv, carrier, with_huc);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, func_ty, with_a)
    };
    let ty = {
        let applied = uc_ty(d, p, neg_fn, a, b);
        let with_huc = d.arrow(huc_ty, applied);
        let with_b = d.pi_fv(b_fv, carrier, with_huc);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, func_ty, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_neg,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `sub` (closure under subtraction) -----------------------------

/// `CReal.uniformly_continuous_sub : ∀ F G a b, UniformlyContinuousOn F a b
/// -> UniformlyContinuousOn G a b -> UniformlyContinuousOn (fun r => add (F
/// r) (neg (G r))) a b` -- pure composition of
/// [`declare_uniformly_continuous_add`] and
/// [`declare_uniformly_continuous_neg`], no new estimate.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_sub(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let huc_f_ty = uc_ty(d, p, f, a, b);
    let huc_f_fv = d.fresh_fvar();
    let huc_f = d.kernel().fvar(huc_f_fv);
    let huc_g_ty = uc_ty(d, p, g, a, b);
    let huc_g_fv = d.fresh_fvar();
    let huc_g = d.kernel().fvar(huc_g_fv);

    let neg_g_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let gr = d.apply(g, &[r]);
        let ngr = cneg(d, p, gr);
        d.lam_fv(r_fv, carrier, ngr)
    };

    let huc_neg_g = d.lemma(p.uniformly_continuous_neg, &[g, a, b, huc_g]);
    let body = d.lemma(
        p.uniformly_continuous_add,
        &[f, neg_g_fn, a, b, huc_f, huc_neg_g],
    );

    let sub_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let ngr = d.apply(neg_g_fn, &[r]);
        let diff = cadd(d, p, fr, ngr);
        d.lam_fv(r_fv, carrier, diff)
    };

    let value = {
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, body);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_b = d.lam_fv(b_fv, carrier, with_huc_f);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let concl = uc_ty(d, p, sub_fn, a, b);
        let with_huc_g = d.arrow(huc_g_ty, concl);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_b = d.pi_fv(b_fv, carrier, with_huc_f);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_sub,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `mul` (closure under multiplication, `BoundedOn`-gated) ------

/// `CReal.uniformly_continuous_mul : ∀ F G a b, UniformlyContinuousOn F a b
/// -> UniformlyContinuousOn G a b -> ∀ k1 k2, BoundedOn F a b k1 -> BoundedOn
/// G a b k2 -> UniformlyContinuousOn (fun r => mul (F r) (G r)) a b`.
///
/// ## The estimate, worked on paper first
///
/// `F(x)G(x) - F(y)G(y) = F(x)(G(x)-G(y)) + G(y)(F(x)-F(y))`
/// ([`product_diff_identity`]), so with `|F(x)| <= k1+1` and `|G(y)| <= k2+1`
/// ([`BoundedOn`]):
///
/// `|F(x)G(x)-F(y)G(y)| <= (k1+1)|G(x)-G(y)| + (k2+1)|F(x)-F(y)|`
/// ([`abs_mul_le_of_bounds`](super::CRealPrelude::abs_mul_le_of_bounds) at
/// each term, via the two-sided identity's own triangle inequality
/// [`abs_add_le`]).
///
/// Target accuracy `n` needs `1/(n+1)` total, split as two `1/(2n+2)`
/// shares exactly [`declare_uniformly_continuous_add`]'s own two-way split
/// (`m := succ(2n)`). Each share must absorb its OWN magnitude weight:
/// `(k1+1) * X <= 1/(2n+2)` needs `X <= 1/((k1+1)(2n+2))`, gotten from `G`'s
/// own spec at accuracy `e_g := rescale_index(k1, m) = (k1+1)*m + k1`, since
/// `Rat.natDivSucc_scale` reads `(k1+1)/(e_g+1)` back down to `1/(m+1)`
/// exactly ([`fold_mag_bound_error`] -- concretely, with `k1 = 0`, `m = 3`
/// (accuracy `n=1`): `e_g = 1*3+0 = 3`, and `(0+1)/(3+1) = 1/4 = natDivSucc
/// 1 3`, matching `m=3` on the nose). Symmetrically `e_f :=
/// rescale_index(k2, m)` for `F`'s own spec, weighted by `k2` (`G`'s bound,
/// since term two is `G(y)*(F(x)-F(y))`). The combined modulus is
/// `mG(e_g) + mF(e_f)`, weakened down to each factor's own hypothesis by
/// `Nat.le_add_right` + `Rat.natDivSucc_antitone`, the identical recipe
/// [`declare_uniformly_continuous_add`] uses for its own two-source modulus
/// (`Nat.add_comm` handles the second, symmetric, direction).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_uniformly_continuous_mul(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let huc_f_ty = uc_ty(d, p, f, a, b);
    let huc_f_fv = d.fresh_fvar();
    let huc_f = d.kernel().fvar(huc_f_fv);
    let huc_g_ty = uc_ty(d, p, g, a, b);
    let huc_g_fv = d.fresh_fvar();
    let huc_g = d.kernel().fvar(huc_g_fv);

    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);

    let hbf_ty = bounded_on_applied(d, p, f, a, b, k1);
    let hbf_fv = d.fresh_fvar();
    let hbf = d.kernel().fvar(hbf_fv);
    let hbg_ty = bounded_on_applied(d, p, g, a, b, k2);
    let hbg_fv = d.fresh_fvar();
    let hbg = d.kernel().fvar(hbg_fv);

    let mul_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let prod = cmul(d, p, fr, gr);
        d.lam_fv(r_fv, carrier, prod)
    };

    let mf = d.const_app(p.uc_modulus, &[f, a, b, huc_f]);
    let mg = d.const_app(p.uc_modulus, &[g, a, b, huc_g]);

    let m_of = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let two = d.num(2);
        let two_n = d.mul(two, n);
        d.succ(two_n)
    };

    let modulus_mul = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m = m_of(d, n);
        let e_g = rescale_index(d, k1, m);
        let e_f = rescale_index(d, k2, m);
        let mg_eg = d.apply(mg, &[e_g]);
        let mf_ef = d.apply(mf, &[e_f]);
        let sum = d.add(mg_eg, mf_ef);
        d.lam_fv(n_fv, nat, sum)
    };

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);
        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);

        let m = m_of(d, n);
        let e_g = rescale_index(d, k1, m);
        let e_f = rescale_index(d, k2, m);
        let mg_eg = d.apply(mg, &[e_g]);
        let mf_ef = d.apply(mf, &[e_f]);
        let combined = d.add(mg_eg, mf_ef);

        let mod_n = d.apply(modulus_mul, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x, y, in_bound);
        let h = d.kernel().fvar(h_fv);

        // --- weaken `h` down to G's and F's own hypotheses, the
        // `uniformly_continuous_add` recipe verbatim. -----------------------
        let nat_p = p.rat.int.nat;
        let h_le_g = d.lemma(nat_p.le_add_right, &[mg_eg, mf_ef]); // Le mg_eg combined
        let mf_plus_mg = d.add(mf_ef, mg_eg);
        let raw_f = d.lemma(nat_p.le_add_right, &[mf_ef, mg_eg]); // Le mf_ef mf_plus_mg
        let comm_eq = d.lemma(nat_p.add_comm, &[mf_ef, mg_eg]); // Eq mf_plus_mg combined
        let h_le_f = nat_rewrite_prop(d, mf_plus_mg, combined, comm_eq, raw_f, &|d, t| {
            NatOps::le(d, mf_ef, t)
        });

        let r_g = div_succ(d, p, 1, mg_eg);
        let r_f = div_succ(d, p, 1, mf_ef);
        let r_combined = div_succ(d, p, 1, combined);
        let rat_g = d.lemma(p.rat.nat_div_succ_antitone, &[mg_eg, combined, h_le_g]);
        let rat_f = d.lemma(p.rat.nat_div_succ_antitone, &[mf_ef, combined, h_le_f]);

        let ofr_combined = d.const_app(p.of_rat, &[r_combined]);
        let ofr_g = d.const_app(p.of_rat, &[r_g]);
        let ofr_f = d.const_app(p.of_rat, &[r_f]);
        let creal_g = d.lemma(p.of_rat_le, &[r_combined, r_g, rat_g]);
        let creal_f = d.lemma(p.of_rat_le, &[r_combined, r_f, rat_f]);

        let ny = cneg(d, p, y);
        let diff_xy = cadd(d, p, x, ny);
        let abs_diff = cabs(d, p, diff_xy);
        let hyp_g = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_g, h, creal_g]);
        let hyp_f = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_f, h, creal_f]);
        // hyp_g : close_within x y r_g ; hyp_f : close_within x y r_f

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);

        let spec_g = d.const_app(p.uc_spec, &[g, a, b, huc_g]);
        let spec_f = d.const_app(p.uc_spec, &[f, a, b, huc_f]);
        let close_g = d.apply(spec_g, &[e_g, x, y, hax, hxb, hay, hyb, hyp_g]);
        let close_f = d.apply(spec_f, &[e_f, x, y, hax, hxb, hay, hyb, hyp_f]);
        // close_g : le (abs (add gx (neg gy))) (ofRat (natDivSucc 1 e_g))
        // close_f : le (abs (add fx (neg fy))) (ofRat (natDivSucc 1 e_f))

        let hbf_x = d.apply(hbf, &[x, hax, hxb]); // le (abs fx) (mag_bound k1)
        let hbg_y = d.apply(hbg, &[y, hay, hyb]); // le (abs gy) (mag_bound k2)

        let (term1, term2, target, diff_proof) = product_diff_identity(d, p, fx, fy, gx, gy);
        let abs_term1 = cabs(d, p, term1);
        let abs_term2 = cabs(d, p, term2);

        // --- term1 := mul fx (add gx (neg gy)), bounded by
        // ofRat(natDivSucc 1 m) -------------------------------------------
        let neg_gy = cneg(d, p, gy);
        let diff_g = cadd(d, p, gx, neg_gy);
        let abs_diff_g = cabs(d, p, diff_g);
        let refl_absdiffg = d.lemma(p.le_refl, &[abs_diff_g]);
        let (fold1_big, fold1_small, fold1_out, fold1_proof) =
            fold_mag_bound_error(d, p, k1, m, e_g);
        let term1_abs_le_prod = d.lemma(
            p.abs_mul_le_of_bounds,
            &[fx, diff_g, fold1_big, abs_diff_g, hbf_x, refl_absdiffg],
        );
        // term1_abs_le_prod : le (abs term1) (mul fold1_big abs_diff_g)
        let magk1_nonneg = mag_bound_nonneg(d, p, k1);
        let scaled_g = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[fold1_big, abs_diff_g, fold1_small, magk1_nonneg, close_g],
        );
        // scaled_g : le (mul fold1_big abs_diff_g) (mul fold1_big fold1_small)
        let mul_fold1 = cmul(d, p, fold1_big, abs_diff_g);
        let mul_fold1_small = cmul(d, p, fold1_big, fold1_small);
        let term1_le_unfused = d.lemma(
            p.le_trans,
            &[
                abs_term1,
                mul_fold1,
                mul_fold1_small,
                term1_abs_le_prod,
                scaled_g,
            ],
        );
        // term1_le_unfused : le (abs term1) (mul fold1_big fold1_small)
        let refl_absterm1 = erefl(d, p, abs_term1);
        let final1 = d.lemma(
            p.le_congr,
            &[
                abs_term1,
                abs_term1,
                mul_fold1_small,
                fold1_out,
                refl_absterm1,
                fold1_proof,
                term1_le_unfused,
            ],
        );
        // final1 : le (abs term1) fold1_out,  fold1_out = ofRat(natDivSucc 1 m)

        // --- term2 := mul gy (add fx (neg fy)), symmetric ------------------
        let neg_fy = cneg(d, p, fy);
        let diff_f = cadd(d, p, fx, neg_fy);
        let abs_diff_f = cabs(d, p, diff_f);
        let refl_absdifff = d.lemma(p.le_refl, &[abs_diff_f]);
        let (fold2_big, fold2_small, fold2_out, fold2_proof) =
            fold_mag_bound_error(d, p, k2, m, e_f);
        let term2_abs_le_prod = d.lemma(
            p.abs_mul_le_of_bounds,
            &[gy, diff_f, fold2_big, abs_diff_f, hbg_y, refl_absdifff],
        );
        let magk2_nonneg = mag_bound_nonneg(d, p, k2);
        let scaled_f = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[fold2_big, abs_diff_f, fold2_small, magk2_nonneg, close_f],
        );
        let mul_fold2 = cmul(d, p, fold2_big, abs_diff_f);
        let mul_fold2_small = cmul(d, p, fold2_big, fold2_small);
        let term2_le_unfused = d.lemma(
            p.le_trans,
            &[
                abs_term2,
                mul_fold2,
                mul_fold2_small,
                term2_abs_le_prod,
                scaled_f,
            ],
        );
        let refl_absterm2 = erefl(d, p, abs_term2);
        let final2 = d.lemma(
            p.le_congr,
            &[
                abs_term2,
                abs_term2,
                mul_fold2_small,
                fold2_out,
                refl_absterm2,
                fold2_proof,
                term2_le_unfused,
            ],
        );
        // final2 : le (abs term2) fold2_out, fold2_out ALSO = ofRat(natDivSucc 1 m)

        // --- triangle inequality + fuse the two `1/(m+1)` shares into
        // `1/(n+1)`, the `uniformly_continuous_add` tail verbatim. ----------
        let sum_bounds = d.lemma(
            p.add_le_add,
            &[abs_term1, fold1_out, abs_term2, fold2_out, final1, final2],
        );
        let triangle = d.lemma(p.abs_add_le, &[term1, term2]);
        let sum_term1_term2 = cadd(d, p, term1, term2);
        let abs_sum = cabs(d, p, sum_term1_term2);
        let sum_of_abs = cadd(d, p, abs_term1, abs_term2);
        let fold1_out_plus_fold1_out = cadd(d, p, fold1_out, fold2_out);
        let combined_le = d.lemma(
            p.le_trans,
            &[
                abs_sum,
                sum_of_abs,
                fold1_out_plus_fold1_out,
                triangle,
                sum_bounds,
            ],
        );
        // combined_le : le abs_sum (add fold1_out fold2_out),
        //   fold1_out = fold2_out = ofRat(natDivSucc 1 m)

        let one_nat = d.num(1);
        let r_prime = div_succ(d, p, 1, m); // == the rational inside fold1_out/fold2_out
        let of_rat_add_proof = d.lemma(p.of_rat_add, &[r_prime, r_prime]);
        let eq1 = d.lemma(p.rat.nat_div_succ_add, &[one_nat, one_nat, m]);
        let two_m = div_succ(d, p, 2, m);
        let radd_r_prime_r_prime = radd(d, r_prime, r_prime);
        let step_a = rat_eq_rewrite(
            d,
            radd_r_prime_r_prime,
            two_m,
            eq1,
            of_rat_add_proof,
            &|d, t| {
                let oft = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[fold1_out_plus_fold1_out, oft])
            },
        );
        let eq2 = d.lemma(p.rat.nat_div_succ_halve, &[n]);
        let out_bound_rat = div_succ(d, p, 1, n);
        let fuse_equiv = rat_eq_rewrite(d, two_m, out_bound_rat, eq2, step_a, &|d, t| {
            let oft = d.const_app(p.of_rat, &[t]);
            d.const_app(p.equiv, &[fold1_out_plus_fold1_out, oft])
        });
        // fuse_equiv : Equiv fold1_out_plus_fold1_out (ofRat out_bound_rat)
        let ofr_out_bound = d.const_app(p.of_rat, &[out_bound_rat]);

        let refl_abssum = erefl(d, p, abs_sum);
        let fused = d.lemma(
            p.le_congr,
            &[
                abs_sum,
                abs_sum,
                fold1_out_plus_fold1_out,
                ofr_out_bound,
                refl_abssum,
                fuse_equiv,
                combined_le,
            ],
        );
        // fused : le abs_sum ofr_out_bound

        // --- lift through the algebraic identity `sum_term1_term2 ~ target`
        let abs_target = cabs(d, p, target);
        let target_equiv = d.lemma(p.abs_congr, &[sum_term1_term2, target, diff_proof]);
        let refl_ofr_out_bound = erefl(d, p, ofr_out_bound);
        let result = d.lemma(
            p.le_congr,
            &[
                abs_sum,
                abs_target,
                ofr_out_bound,
                ofr_out_bound,
                target_equiv,
                refl_ofr_out_bound,
                fused,
            ],
        );
        // result : le abs_target ofr_out_bound
        //   == close_within (mul_fn x) (mul_fn y) out_bound_rat

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[mul_fn, a, b, modulus_mul, spec]);
    let value = {
        let with_hbg = d.lam_fv(hbg_fv, hbg_ty, mk_applied);
        let with_hbf = d.lam_fv(hbf_fv, hbf_ty, with_hbg);
        let with_k2 = d.lam_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.lam_fv(k1_fv, nat, with_k2);
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, with_k1);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_b = d.lam_fv(b_fv, carrier, with_huc_f);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let applied = uc_ty(d, p, mul_fn, a, b);
        let with_hbg = d.arrow(hbg_ty, applied);
        let with_hbf = d.arrow(hbf_ty, with_hbg);
        let with_k2 = d.pi_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.pi_fv(k1_fv, nat, with_k2);
        let with_huc_g = d.arrow(huc_g_ty, with_k1);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_b = d.pi_fv(b_fv, carrier, with_huc_f);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_mul,
        uparams: vec![],
        ty,
        value,
    })
}

// --- corollary: `sq` ---------------------------------------------------------

/// `CReal.uniformly_continuous_sq : ∀ a b k, BoundedOn (fun r => r) a b k ->
/// UniformlyContinuousOn (fun r => mul r r) a b` -- `mul` specialised to `F
/// := G := id`, both bound witnesses the SAME `BoundedOn id a b k`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_sq(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let huc_id = d.lemma(p.uniformly_continuous_id, &[a, b]);
    let hb_ty = bounded_on_applied(d, p, identity, a, b, k);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let body = d.lemma(
        p.uniformly_continuous_mul,
        &[identity, identity, a, b, huc_id, huc_id, k, k, hb, hb],
    );

    let sq_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let ir = d.apply(identity, &[r]);
        let ir2 = d.apply(identity, &[r]);
        let prod = cmul(d, p, ir, ir2);
        d.lam_fv(r_fv, carrier, prod)
    };

    let value = {
        let with_hb = d.lam_fv(hb_fv, hb_ty, body);
        let with_k = d.lam_fv(k_fv, nat, with_hb);
        let with_b = d.lam_fv(b_fv, carrier, with_k);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let concl = uc_ty(d, p, sq_fn, a, b);
        let with_hb = d.arrow(hb_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, with_hb);
        let with_b = d.pi_fv(b_fv, carrier, with_k);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_sq,
        uparams: vec![],
        ty,
        value,
    })
}

// --- concrete instantiation --------------------------------------------------

/// `CReal.bounded_on_id_unit : BoundedOn (fun r => r) zero (mag_bound 0) 0`
/// -- `id` bounded by `1` on `[0, mag_bound 0]`, where `mag_bound 0 = ofRat
/// (natDivSucc 1 0)` IS the kernel's own representation of the real number
/// `1` (chosen, rather than a separate `CReal.one` endpoint, so this proof
/// needs no bridge lemma between the two: `0 <= z <= mag_bound 0` gives `abs
/// z <= mag_bound 0` directly via `abs_le`, since `neg z <= zero <=
/// mag_bound 0`).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bounded_on_id_unit(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero_c = czero(d, p);
    let zero_idx = d.num(0);
    let unit = mag_bound(d, p, zero_idx);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let haz_fv = d.fresh_fvar();
    let haz = d.kernel().fvar(haz_fv);
    let hzb_fv = d.fresh_fvar();
    let hzb = d.kernel().fvar(hzb_fv);

    let range_az = d.const_app(p.le, &[zero_c, z]);
    let range_zb = d.const_app(p.le, &[z, unit]);

    // le (neg z) unit: neg z <= zero (from 0<=z via neg_le_neg + `neg zero ~
    // zero` unfolds by `CReal.zero`'s own defeq to `ofRat Rat.zero`, so
    // `neg zero` and `zero` need `equiv_of_le_le`-free handling) then
    // zero <= unit (mag_bound_nonneg).
    let neg_z = cneg(d, p, z);
    let neg_zero = cneg(d, p, zero_c);
    let negz_le_negzero = d.lemma(p.neg_le_neg, &[zero_c, z, haz]);
    // negz_le_negzero : le (neg z) (neg zero)
    let rzero_expr = crate::rat_prelude::ops::rzero(d, p.rat);
    let ofr_zero = d.const_app(p.of_rat, &[rzero_expr]);
    let of_rat_neg_at_zero = d.lemma(p.of_rat_neg, &[rzero_expr]);
    // of_rat_neg_at_zero : Equiv (neg ofr_zero) (ofRat (Rat.neg rzero_expr))
    let neg_rzero_expr = crate::rat_prelude::ops::rneg(d, rzero_expr);
    let rat_neg_zero_eq = d.lemma(p.rat.neg_zero, &[]);
    // rat_neg_zero_eq : Eq Rat (Rat.neg rzero_expr) rzero_expr
    let neg_zero_equiv_zero = rat_eq_rewrite(
        d,
        neg_rzero_expr,
        rzero_expr,
        rat_neg_zero_eq,
        of_rat_neg_at_zero,
        &|d, t| {
            let oft = d.const_app(p.of_rat, &[t]);
            d.const_app(p.equiv, &[neg_zero, oft])
        },
    );
    // neg_zero_equiv_zero : Equiv neg_zero ofr_zero
    let refl_negz = erefl(d, p, neg_z);
    let negz_le_ofrzero = d.lemma(
        p.le_congr,
        &[
            neg_z,
            neg_z,
            neg_zero,
            ofr_zero,
            refl_negz,
            neg_zero_equiv_zero,
            negz_le_negzero,
        ],
    );
    // negz_le_ofrzero : le neg_z ofr_zero -- and `ofr_zero` is defeq to `zero_c`
    let zero_le_unit = mag_bound_nonneg(d, p, zero_idx);
    let negz_le_unit = d.lemma(
        p.le_trans,
        &[neg_z, ofr_zero, unit, negz_le_ofrzero, zero_le_unit],
    );

    let body = d.lemma(p.abs_le, &[z, unit, hzb, negz_le_unit]);

    let value = {
        let with_hzb = d.lam_fv(hzb_fv, range_zb, body);
        let with_haz = d.lam_fv(haz_fv, range_az, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };
    let ty = {
        let concl = {
            let iz = d.apply(identity, &[z]);
            let abs_iz = cabs(d, p, iz);
            d.const_app(p.le, &[abs_iz, unit])
        };
        let with_zb = d.arrow(range_zb, concl);
        let with_az = d.arrow(range_az, with_zb);
        d.pi_fv(z_fv, carrier, with_az)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bounded_on_id_unit,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`CRealPrelude::bounded_on_id_zero_one`] — `BoundedOn (fun r => r)
/// zero one 0`, i.e. `∀ z, le zero z → le z one → le (abs z) (mag_bound
/// 0)`. `id` bounded by `1` on the ORDINARY unit interval `[0, 1]`, unlike
/// [`declare_bounded_on_id_unit`]'s `[0, mag_bound 0]` (`mag_bound 0` is
/// the kernel's own representation of `1`, chosen there so that proof needs
/// no bridge lemma). This is the bridge lemma
/// [`declare_bounded_on_id_unit`]'s own doc comment says is unneeded for
/// ITS interval and IS needed for `[0, 1]`: `Equiv one (mag_bound 0)`, via
/// [`CRealPrelude::rat_unit_eq_one`] (`Eq Rat (natDivSucc 1 0) Rat.one`)
/// lifted across `CReal.ofRat` — the same `rat_eq_rewrite`-with-an-`Equiv`-
/// motive idiom [`declare_bounded_on_id_unit`] already uses for `neg zero ~
/// zero`.
///
/// Once `hzb : le z one` is transported to `le z (mag_bound 0)`, this
/// applies [`CRealPrelude::bounded_on_id_unit`] DIRECTLY at `(z, haz,
/// hzb')` rather than re-deriving `neg z ≤ mag_bound 0` a second time — the
/// "promote, don't duplicate" the private helper
/// [`crate::CRealPrelude::abs_bound_of_self`] above illustrates on a wider
/// scale, applied here to a single sibling theorem instead of a whole
/// prelude field.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_bounded_on_id_zero_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero_c = czero(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_idx = d.num(0);
    let mag0 = mag_bound(d, p, zero_idx);

    // Bridge: `Equiv one mag0`, via `rat_unit_eq_one : Eq Rat (natDivSucc 1
    // 0) Rat.one` lifted across `ofRat`. `unit_rat` is built by the same
    // two calls `mag_bound` uses internally, so it interns to the exact
    // `ExprId` `mag_bound`'s own `ofRat` argument does.
    let succ_zero = d.succ(zero_idx);
    let unit_rat = div_succ_at(d, p, succ_zero, zero_idx); // natDivSucc 1 0
    let one_rat = crate::rat_prelude::ops::rone(d, p.rat);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]); // Eq Rat unit_rat one_rat
    let refl_mag0 = erefl(d, p, mag0);
    let one_equiv_mag0 = rat_eq_rewrite(d, unit_rat, one_rat, unit_eq_one, refl_mag0, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, embedded, mag0)
    });
    // one_equiv_mag0 : Equiv (ofRat one_rat) mag0 -- defeq Equiv one mag0.

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let haz_fv = d.fresh_fvar();
    let haz = d.kernel().fvar(haz_fv);
    let hzb_fv = d.fresh_fvar();
    let hzb = d.kernel().fvar(hzb_fv);

    let range_az = cle(d, p, zero_c, z);
    let range_zb = cle(d, p, z, one_c);

    let refl_z = erefl(d, p, z);
    let hzb_mag0 = d.lemma(
        p.le_congr,
        &[z, z, one_c, mag0, refl_z, one_equiv_mag0, hzb],
    );
    // hzb_mag0 : le z mag0

    // Reuse `bounded_on_id_unit` directly rather than re-deriving `neg z <=
    // mag0`.
    let bou = d.kernel().const_(p.bounded_on_id_unit, vec![]);
    let body = d.apply(bou, &[z, haz, hzb_mag0]);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let value = {
        let with_hzb = d.lam_fv(hzb_fv, range_zb, body);
        let with_haz = d.lam_fv(haz_fv, range_az, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };
    let ty = {
        let concl = {
            let iz = d.apply(identity, &[z]);
            let abs_iz = cabs(d, p, iz);
            d.const_app(p.le, &[abs_iz, mag0])
        };
        let with_zb = d.arrow(range_zb, concl);
        let with_az = d.arrow(range_az, with_zb);
        d.pi_fv(z_fv, carrier, with_az)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bounded_on_id_zero_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.uniformly_continuous_poly_example : UniformlyContinuousOn (fun r
/// => add (add (mul r r) r) one) zero (mag_bound 0)` -- the concrete payoff:
/// `x -> x^2 + x + 1` uniformly continuous on `[0,1]` (`mag_bound 0` IS the
/// kernel's own `1`, see [`declare_bounded_on_id_unit`]), assembled from
/// [`declare_uniformly_continuous_sq`], [`declare_uniformly_continuous_id`],
/// [`declare_uniformly_continuous_const`] and
/// [`declare_uniformly_continuous_add`] with EVERY `BoundedOn` hypothesis
/// discharged concretely (both factors of `sq` are `id`, bounded by
/// [`declare_bounded_on_id_unit`]) rather than left universally quantified.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_poly_example(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero_c = czero(d, p);
    let zero_idx = d.num(0);
    let unit = mag_bound(d, p, zero_idx);
    let one_c = d.kernel().const_(p.one, vec![]);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let huc_id = d.lemma(p.uniformly_continuous_id, &[zero_c, unit]);
    let hb_id = d.lemma(p.bounded_on_id_unit, &[]);

    let huc_sq = d.lemma(p.uniformly_continuous_sq, &[zero_c, unit, zero_idx, hb_id]);
    // huc_sq : UniformlyContinuousOn (fun r => mul (id r) (id r)) zero unit

    let sq_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let ir = d.apply(identity, &[r]);
        let ir2 = d.apply(identity, &[r]);
        let prod = cmul(d, p, ir, ir2);
        d.lam_fv(r_fv, carrier, prod)
    };

    let huc_sq_plus_id = d.lemma(
        p.uniformly_continuous_add,
        &[sq_fn, identity, zero_c, unit, huc_sq, huc_id],
    );
    // huc_sq_plus_id : UniformlyContinuousOn (fun r => add (sq_fn r) (id r)) zero unit

    let sq_plus_id_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let sqr = d.apply(sq_fn, &[r]);
        let ir = d.apply(identity, &[r]);
        let sum = cadd(d, p, sqr, ir);
        d.lam_fv(r_fv, carrier, sum)
    };

    let huc_const_one = d.lemma(p.uniformly_continuous_const, &[one_c, zero_c, unit]);

    let const_one_fn = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };
    let huc_poly = d.lemma(
        p.uniformly_continuous_add,
        &[
            sq_plus_id_fn,
            const_one_fn,
            zero_c,
            unit,
            huc_sq_plus_id,
            huc_const_one,
        ],
    );
    // huc_poly : UniformlyContinuousOn
    //   (fun r => add (sq_plus_id_fn r) (const_one_fn r)) zero unit

    let poly_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let spr = d.apply(sq_plus_id_fn, &[r]);
        let sum = cadd(d, p, spr, one_c);
        d.lam_fv(r_fv, carrier, sum)
    };
    let ty = uc_ty(d, p, poly_fn, zero_c, unit);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_poly_example,
        uparams: vec![],
        ty,
        value: huc_poly,
    })
}

// --- the running bound over finitely many sample points ---------------------
//
// `CReal.bounded_of_uniformly_continuous` (the boundedness-of-uniformly-
// continuous-functions theorem, not landed here -- see the module
// documentation) needs, at its last step, a SINGLE `Nat` `k` bounding
// `|F(x_i)|` at every one of finitely many sample points `x_0, …, x_N`. Each
// `|F(x_i)|` is bounded by SOME `mag_bound (g i)` (`g` built from
// `CReal.bound`, a total computable projection -- no search), but picking
// the LARGEST of finitely many `Nat`s by comparison is exactly the kind of
// decision `CReal.le` cannot make (`CReal.le` is undecidable; see the module
// documentation's own house rule, echoing `CReal.pos_bound_of_lt`'s). A
// running SUM sidesteps the comparison entirely: a sum of nonnegative reals
// dominates each addend, and nonnegativity of `mag_bound _` is unconditional
// (`mag_bound_nonneg`, below) -- no case split on any two samples' relative
// size is ever needed. This is the finite-sample form of that idea, proved
// once, independent of where the samples come from.

/// `False.rec (fun _ => target) false_proof : target`. Local copy of the
/// identical private helper in `creal/sqrt.rs` (itself a copy of several
/// `nat_prelude` modules' own private `ex_falso`) -- see that copy's own doc
/// comment for the lineage. Reused here rather than threaded across the
/// module boundary, matching this file's existing practice for
/// [`mag_bound`]/[`bounded_on_applied`]/[`rescale_index`] above.
fn ex_falso(d: &mut IntDev<'_>, p: CRealPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let nat_p = p.rat.int.nat;
    let false_ty = d.kernel().const_(nat_p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(nat_p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `le x (add x w)`, from `hw : le zero w`. Local copy of the identical
/// private helper in `creal/monotone.rs` (`shift_le_of_nonneg`), duplicated
/// for the same file-boundary reason as [`ex_falso`] above.
fn shift_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    w: ExprId,
    hw: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let refl_x = d.lemma(p.le_refl, &[x]);
    let grown = d.lemma(p.add_le_add, &[x, x, zero_c, w, refl_x, hw]);
    let padded = cadd(d, p, x, zero_c);
    let target = cadd(d, p, x, w);
    let trim = d.lemma(p.add_zero, &[x]);
    let refl_target = erefl(d, p, target);
    d.lemma(
        p.le_congr,
        &[padded, x, target, target, trim, refl_target, grown],
    )
}

/// `CReal.le CReal.zero (CReal.sumRange f n)`, where `f := fun j => mag_bound
/// (g j)` for the SAME `g` used by [`declare_mag_bound_le_sum_range_of_lt`].
///
/// By induction on `n`: base case `sumRange f 0 ≡ zero` (`Nat.rec`'s own
/// ι-reduction, matching this file's existing convention — see
/// [`declare_mag_bound_le_sum_range_of_lt`]'s own module documentation), so
/// `le_refl zero` closes it directly against the defeq-unfolded goal.
/// Successor case: `sumRange f (Nat.succ m) ≡ add (sumRange f m) (f m)`
/// (again by raw ι-reduction, no named `sumRange_succ` lemma needed); both
/// summands are nonnegative — the accumulated sum by the induction
/// hypothesis, `f m = mag_bound (g m)` by [`mag_bound_nonneg`] — so
/// [`shift_le_of_nonneg`] extends `le zero (sumRange f m)` across the new
/// term and [`CRealPrelude::le_trans`] chains it from `zero`.
///
/// This is the nonnegativity fact `mag_bound_le_sum_range_of_lt`'s own
/// `minor_equal` branch actually needs as its `shift_le_of_nonneg` witness —
/// nonnegativity of the RUNNING SUM `sum_f_m`, not of the single term
/// `mag_gm` being added to it (those are different propositions, and using
/// the latter where the former is required is exactly the `TypeMismatch`
/// this development hit on its first attempt: `shift_le_of_nonneg(d, p, x,
/// w, hw)` needs `hw : le zero w`, and at that call site `x = mag_gm`, `w =
/// sum_f_m`, so `hw` must be nonnegativity of `sum_f_m`).
fn mag_bound_sum_range_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    g: ExprId,
    f: ExprId,
    n: ExprId,
) -> ExprId {
    let stmt_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let zero_c = czero(d, p);
        let sx = d.const_app(p.sum_range, &[f, x]);
        d.const_app(p.le, &[zero_c, sx])
    };
    d.induct(
        &stmt_at,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_c = czero(d, p);
            d.lemma(p.le_refl, &[zero_c])
        },
        &|d: &mut IntDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
            let gm = d.apply(g, &[m]);
            let mag_gm = mag_bound(d, p, gm);
            let sum_f_m = d.const_app(p.sum_range, &[f, m]);
            let nonneg_fm = mag_bound_nonneg(d, p, gm);
            // le sum_f_m (add sum_f_m mag_gm) -- defeq `sumRange f (succ m)`.
            let step = shift_le_of_nonneg(d, p, sum_f_m, mag_gm, nonneg_fm);
            let zero_c = czero(d, p);
            let target = cadd(d, p, sum_f_m, mag_gm);
            d.lemma(p.le_trans, &[zero_c, sum_f_m, target, ih, step])
        },
        n,
    )
}

/// `CReal.mag_bound_le_sum_range_of_lt : ∀ (g : Nat → Nat) (n i : Nat),
/// Nat.lt i n → CReal.le (mag_bound (g i)) (CReal.sumRange (fun j =>
/// mag_bound (g j)) n)`.
///
/// The `CReal`-valued analogue of `Nat.le_sumRange_of_lt`
/// (`nat_prelude/binomial.rs::declare_le_sum_range_of_lt`), whose proof
/// shape this mirrors almost verbatim: induction on `n` with `i`
/// generalized inside the motive, successor case split by
/// `Nat.lt_or_eq_of_le` into a strict branch (extend the outer induction
/// hypothesis past the new boundary term via [`shift_le_of_nonneg`] +
/// `CReal.le_trans`) and an equal branch (rewrite the goal's sample index
/// from `m` to `i` via `Eq Nat i m`, using [`nat_rewrite_prop`] since the
/// rewritten proposition is `Prop`-valued regardless of the `CReal`-typed
/// terms it mentions -- `NatOps::congr`'s own `Eq` is hardcoded to `Nat`
/// and cannot be used to equate two `CReal`s directly).
///
/// The base case (`n = 0`) is vacuous (`Nat.lt i 0` is impossible,
/// `Nat.not_lt_zero`), regardless of what `CReal.sumRange f 0` reduces to.
///
/// Every step relies on `CReal.sumRange f (Nat.succ n) ≡ add (sumRange f n)
/// (f n)` holding by raw `Nat.rec` ι-reduction (`series.rs::sum_range_succ`'s
/// own proof is `Eq.refl` alone, for the same reason) -- the proof below
/// never invokes `sumRange_succ` as a named lemma, exactly as
/// `Nat.le_sumRange_of_lt`'s own proof never invokes `Nat.sumRange_succ`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
fn declare_mag_bound_le_sum_range_of_lt(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;
    let g_ty = nat_fn_ty(d);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    // f := fun j => mag_bound (g j) : Nat -> CReal.
    let f = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let gj = d.apply(g, &[j]);
        let mbj = mag_bound(d, p, gj);
        d.lam_fv(j_fv, nat, mbj)
    };

    let stmt_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hyp = d.lt(i, x);
        let gi = d.apply(g, &[i]);
        let mbi = mag_bound(d, p, gi);
        let sx = d.const_app(p.sum_range, &[f, x]);
        let concl = d.const_app(p.le, &[mbi, sx]);
        let body = d.arrow(hyp, concl);
        d.pi_fv(i_fv, nat, body)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt = stmt_at(d, n);

    let proof = d.induct(
        &stmt_at,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_nat = d.num(0);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp_ty = d.lt(i, zero_nat);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let not_lt = d.lemma(nat_p.not_lt_zero, &[i]);
            let false_proof = d.apply(not_lt, &[h]);

            let gi = d.apply(g, &[i]);
            let mbi = mag_bound(d, p, gi);
            let sum0 = d.const_app(p.sum_range, &[f, zero_nat]);
            let target = d.const_app(p.le, &[mbi, sum0]);

            let body = ex_falso(d, p, target, false_proof);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(i_fv, nat, with_h)
        },
        &|d: &mut IntDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
            let sm = d.succ(m);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp_ty = d.lt(i, sm);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // Nat.lt i (succ m) is defeq Nat.le (succ i) (succ m); peel to
            // Nat.le i m, then split it.
            let h_le_im = d.lemma(nat_p.le_of_succ_le_succ, &[i, m, h]);
            let split = d.lemma(nat_p.lt_or_eq_of_le, &[i, m, h_le_im]);

            let strict_ty = d.lt(i, m);
            let equal_ty = d.eq(i, m);

            let gm = d.apply(g, &[m]);
            let mag_gm = mag_bound(d, p, gm);
            let sum_f_m = d.const_app(p.sum_range, &[f, m]);
            // add sum_f_m mag_gm -- defeq `sumRange f (succ m)`.
            let lhs2 = cadd(d, p, sum_f_m, mag_gm);

            let gi = d.apply(g, &[i]);
            let mag_gi = mag_bound(d, p, gi);
            let target = d.const_app(p.le, &[mag_gi, lhs2]);

            let minor_strict = {
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);
                let ih_i = d.apply(ih, &[i, hlt]); // le mag_gi sum_f_m
                let nonneg_gm = mag_bound_nonneg(d, p, gm);
                let ext = shift_le_of_nonneg(d, p, sum_f_m, mag_gm, nonneg_gm); // le sum_f_m lhs2
                let body = d.lemma(p.le_trans, &[mag_gi, sum_f_m, lhs2, ih_i, ext]);
                d.lam_fv(hlt_fv, strict_ty, body)
            };
            let minor_equal = {
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);
                let sym_heq = d.symm(i, m, heq); // Eq Nat m i

                let nonneg_sum_f_m = mag_bound_sum_range_nonneg(d, p, g, f, m);
                // le mag_gm (add mag_gm sum_f_m)
                let h1 = shift_le_of_nonneg(d, p, mag_gm, sum_f_m, nonneg_sum_f_m);
                let lhs1 = cadd(d, p, mag_gm, sum_f_m);
                let hcomm = d.lemma(p.add_comm, &[mag_gm, sum_f_m]); // Equiv lhs1 lhs2
                let refl_magm = erefl(d, p, mag_gm);
                // le mag_gm lhs2
                let h2 = d.lemma(
                    p.le_congr,
                    &[mag_gm, mag_gm, lhs1, lhs2, refl_magm, hcomm, h1],
                );

                let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                    let gx = d.apply(g, &[x]);
                    let mbx = mag_bound(d, p, gx);
                    d.const_app(p.le, &[mbx, lhs2])
                };
                let body = nat_rewrite_prop(d, m, i, sym_heq, h2, &motive);
                d.lam_fv(heq_fv, equal_ty, body)
            };

            let selected = d.const_app(
                nat_p.logic.or_elim,
                &[
                    strict_ty,
                    equal_ty,
                    target,
                    split,
                    minor_strict,
                    minor_equal,
                ],
            );
            let with_h = d.lam_fv(h_fv, hyp_ty, selected);
            d.lam_fv(i_fv, nat, with_h)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(g_fv, g_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(g_fv, g_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mag_bound_le_sum_range_of_lt,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.mag_bound_le_sum_range_of_lt`. A THIRD entry point (after
/// [`declare_uniform_continuity`] and [`declare_uniform_continuity_products`])
/// because it consumes `CReal.sumRange`, which `series::declare_series`
/// declares after both of those -- see `creal.rs`'s own wiring comment at
/// the call site.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_uniform_continuity_sums(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mag_bound_le_sum_range_of_lt(d, p)
}

// =============================================================================
// `CReal.bounded_of_uniformly_continuous` (Spivak ch.7: a function
// uniformly continuous on `[a,b]` is bounded there) -- the covering
// argument's small algebraic toolkit, then the theorem itself.
//
// See [`declare_bounded_of_uniformly_continuous`]'s own doc comment for the
// overall route. This section is a FOURTH entry point (after
// [`declare_uniform_continuity`], [`declare_uniform_continuity_products`],
// [`declare_uniform_continuity_sums`]) because it consumes `CReal.BoundedOn`
// (`derivative::declare_derivative`) but nothing from `series.rs`.

/// `Nat.le a b -> Rat.le (natDivSucc a 0) (natDivSucc b 0)` -- numerator
/// monotonicity at a FIXED index from an ARBITRARY `Nat.le`, unlike every
/// other numerator widening in this file (which always has a statically
/// visible additive witness). Via `Nat.le_dest` + a non-dependent
/// `Exists.rec`, mirroring `nat_prelude::bezout::succ_witness_elim`'s own
/// pattern (private there, so duplicated here rather than reused across the
/// module boundary).
fn nat_div_succ_le_of_nat_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    hab: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat_p = rat.int.nat;
    let nat = d.nat_ty();
    let zero_nat = d.num(0);
    let one_lvl = d.level_one();
    let anon = d.anon_name();

    let na = div_succ_at(d, p, a, zero_nat);
    let target = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let nx = div_succ_at(d, p, x, zero_nat);
        rle(d, rat, na, nx)
    };

    let represented = d.lemma(nat_p.le_dest, &[a, b, hab]);

    let pred = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let sum = d.add(a, e);
        let body = d.eq(sum, b);
        d.lam_fv(e_fv, nat, body)
    };
    let exists_const = d.kernel().const_(nat_p.logic.exists_, vec![one_lvl]);
    let represented_ty = d.apply(exists_const, &[nat, pred]);
    let target_at_b = target(d, b);
    let motive = d
        .kernel()
        .lam(anon, represented_ty, target_at_b, BinderInfo::Default);

    let minor_term = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let sum = d.add(a, e);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_ty = d.eq(sum, b);

        let widen = d.lemma(rat.nat_div_succ_le_add_left, &[a, e, zero_nat]);
        let rewritten = nat_rewrite_prop(d, sum, b, h, widen, &|d, x| target(d, x));
        let with_h = d.lam_fv(h_fv, h_ty, rewritten);
        d.lam_fv(e_fv, nat, with_h)
    };

    let rec = d.kernel().const_(nat_p.logic.exists_rec, vec![one_lvl]);
    d.apply(rec, &[nat, pred, motive, minor_term, represented])
}

/// `le (mag_bound k1) (mag_bound k2)` from `Nat.le k1 k2`.
fn mag_bound_mono(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k1: ExprId,
    k2: ExprId,
    h: ExprId,
) -> ExprId {
    let nat_p = p.rat.int.nat;
    let sk1 = d.succ(k1);
    let sk2 = d.succ(k2);
    let hs = d.lemma(nat_p.succ_le_succ, &[k1, k2, h]);
    let rat_le = nat_div_succ_le_of_nat_le(d, p, sk1, sk2, hs);
    let zero_nat = d.num(0);
    let b1 = div_succ_at(d, p, sk1, zero_nat);
    let b2 = div_succ_at(d, p, sk2, zero_nat);
    d.lemma(p.of_rat_le, &[b1, b2, rat_le])
}

/// `Equiv (add (mag_bound k) (mag_bound zero)) (mag_bound (succ k))`. The
/// numerator sum is built `succ_k + one` (symbolic LEFT, literal RIGHT) so
/// `Nat.add`'s recursion on its right argument reduces the fused index to
/// `succ (succ k)` by pure computation -- see the module's own hard rule on
/// `Nat.add`/`Nat.mul` operand order.
fn mag_bound_fuse_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let succ_k = d.succ(k);
    let rk = div_succ_at(d, p, succ_k, zero_nat);
    let r0 = div_succ_at(d, p, one_nat, zero_nat);
    let of_rat_add_proof = d.lemma(p.of_rat_add, &[rk, r0]);
    let eq1 = d.lemma(rat.nat_div_succ_add, &[succ_k, one_nat, zero_nat]);
    let sum_rat = radd(d, rk, r0);
    let succ_succ_k = d.succ(succ_k);
    let target_rat = div_succ_at(d, p, succ_succ_k, zero_nat);
    rat_eq_rewrite(d, sum_rat, target_rat, eq1, of_rat_add_proof, &|d, t| {
        let mbk = mag_bound(d, p, k);
        let mb0 = mag_bound(d, p, zero_nat);
        let lhs = cadd(d, p, mbk, mb0);
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[lhs, oft])
    })
}

/// `Equiv (add a (add b (neg a))) b` -- `a + (b - a) ~ b`. Local copy of
/// `creal/monotone.rs::add_sub_cancel` (private there).
fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let start = cadd(d, p, a, width);

    let nab = cadd(d, p, na, b);
    let s1 = cadd(d, p, a, nab);
    let h1 = {
        let comm = d.lemma(p.add_comm, &[b, na]);
        let refl_a = erefl(d, p, a);
        d.lemma(p.add_congr, &[a, a, width, nab, refl_a, comm])
    };

    let ana = cadd(d, p, a, na);
    let s2 = cadd(d, p, ana, b);
    let h2 = {
        let assoc = d.lemma(p.add_assoc, &[a, na, b]);
        esymm(d, p, s2, s1, assoc)
    };

    let zero_c = czero(d, p);
    let s3 = cadd(d, p, zero_c, b);
    let h3 = {
        let hn = d.lemma(p.add_neg, &[a]);
        let refl_b = erefl(d, p, b);
        d.lemma(p.add_congr, &[ana, zero_c, b, b, hn, refl_b])
    };

    let s4 = cadd(d, p, b, zero_c);
    let h4 = d.lemma(p.add_comm, &[zero_c, b]);
    let h5 = d.lemma(p.add_zero, &[b]);

    echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (b, h5)],
    )
}

/// `Equiv (add (add a step) (neg a)) step`. Local copy of
/// `creal/monotone.rs::add_sub_cancel_left` (private there).
fn add_sub_cancel_left(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, step: ExprId) -> ExprId {
    let a_step = cadd(d, p, a, step);
    let na = cneg(d, p, a);
    let start = cadd(d, p, a_step, na);

    let step_a = cadd(d, p, step, a);
    let s1 = cadd(d, p, step_a, na);
    let h1 = {
        let comm = d.lemma(p.add_comm, &[a, step]);
        let refl_na = erefl(d, p, na);
        d.lemma(p.add_congr, &[a_step, step_a, na, na, comm, refl_na])
    };

    let a_na = cadd(d, p, a, na);
    let s2 = cadd(d, p, step, a_na);
    let h2 = d.lemma(p.add_assoc, &[step, a, na]);

    let zero_c = czero(d, p);
    let s3 = cadd(d, p, step, zero_c);
    let h3 = {
        let an = d.lemma(p.add_neg, &[a]);
        let refl_step = erefl(d, p, step);
        d.lemma(p.add_congr, &[step, step, a_na, zero_c, refl_step, an])
    };

    let h4 = d.lemma(p.add_zero, &[step]);

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (step, h4)])
}

/// From `h : le x (add y q)`, derive `le (add x (neg y)) q`.
fn creal_sub_le_of_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let refl_ny = d.lemma(p.le_refl, &[ny]);
    let y_q = cadd(d, p, y, q);
    let step = d.lemma(p.add_le_add, &[x, y_q, ny, ny, h, refl_ny]);
    let yq_ny = cadd(d, p, y_q, ny);
    let cancel = add_sub_cancel_left(d, p, y, q);
    let refl_diff = erefl(d, p, diff);
    d.lemma(p.le_congr, &[diff, diff, yq_ny, q, refl_diff, cancel, step])
}

/// From `h : le (add x (neg y)) q`, derive `le x (add y q)`.
fn creal_le_of_sub_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let refl_y = d.lemma(p.le_refl, &[y]);
    let step = d.lemma(p.add_le_add, &[diff, q, y, y, h, refl_y]);
    let diff_y = cadd(d, p, diff, y);
    let y_diff = cadd(d, p, y, diff);
    let comm = d.lemma(p.add_comm, &[diff, y]);
    let cancel = add_sub_cancel(d, p, y, x);
    let combined = d.lemma(p.equiv_trans, &[diff_y, y_diff, x, comm, cancel]);
    let q_y = cadd(d, p, q, y);
    let refl_qy = erefl(d, p, q_y);
    let raw = d.lemma(p.le_congr, &[diff_y, x, q_y, q_y, combined, refl_qy, step]);
    let y_q = cadd(d, p, y, q);
    let comm2 = d.lemma(p.add_comm, &[q, y]);
    let refl_x = erefl(d, p, x);
    d.lemma(p.le_congr, &[x, x, q_y, y_q, refl_x, comm2, raw])
}

/// `Equiv (neg (add a (neg b))) (add b (neg a))`.
fn neg_sub_swap(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = cneg(d, p, b);
    let na = cneg(d, p, a);
    let a_nb = cadd(d, p, a, nb);
    let n_a_nb = cneg(d, p, a_nb);
    let nnb = cneg(d, p, nb);
    let na_nnb = cadd(d, p, na, nnb);
    let h1 = neg_add(d, p, a, nb);
    let dn = double_neg(d, p, b);
    let na_b = cadd(d, p, na, b);
    let h2 = {
        let refl_na = erefl(d, p, na);
        d.lemma(p.add_congr, &[na, na, nnb, b, refl_na, dn])
    };
    let b_na = cadd(d, p, b, na);
    let h3 = d.lemma(p.add_comm, &[na, b]);
    echain(d, p, n_a_nb, &[(na_nnb, h1), (na_b, h2), (b_na, h3)])
}

/// `close_within x y q`, from `h1 : le x (add y q)` and `h2 : le y (add x q)`.
fn close_of_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let ny = cneg(d, p, y);
    let nx = cneg(d, p, x);
    let diff = cadd(d, p, x, ny);
    let diff2 = cadd(d, p, y, nx);
    let v1 = creal_sub_le_of_le(d, p, x, y, q, h1);
    let v2 = creal_sub_le_of_le(d, p, y, x, q, h2);
    let swap = neg_sub_swap(d, p, x, y);
    let neg_diff = cneg(d, p, diff);
    let swap_rev = esymm(d, p, neg_diff, diff2, swap);
    let refl_q = erefl(d, p, q);
    let h2_final = d.lemma(p.le_congr, &[diff2, neg_diff, q, q, swap_rev, refl_q, v2]);
    d.lemma(p.abs_le, &[diff, q, v1, h2_final])
}

/// From `h : close_within x y q`, derive `close_within y x q`.
fn close_within_symm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let ny = cneg(d, p, y);
    let nx = cneg(d, p, x);
    let diff = cadd(d, p, x, ny);
    let diff2 = cadd(d, p, y, nx);
    let abs_neg_diff_le = abs_neg_le(d, p, diff, q, h);
    let swap = neg_sub_swap(d, p, x, y);
    let neg_diff = cneg(d, p, diff);
    let ac = d.lemma(p.abs_congr, &[neg_diff, diff2, swap]);
    let refl_q = erefl(d, p, q);
    let abs_neg_diff = cabs(d, p, neg_diff);
    let abs_diff2 = cabs(d, p, diff2);
    d.lemma(
        p.le_congr,
        &[abs_neg_diff, abs_diff2, q, q, ac, refl_q, abs_neg_diff_le],
    )
}

/// `Equiv (add (add a u) (neg (add a v))) (add u (neg v))` -- shared-`a`
/// cancellation for a CReal difference of two `a`-shifted terms.
fn shift_diff_cancel(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    u: ExprId,
    v: ExprId,
) -> ExprId {
    let na = cneg(d, p, a);
    let nv = cneg(d, p, v);
    let a_v = cadd(d, p, a, v);
    let n_av = cneg(d, p, a_v);
    let a_u = cadd(d, p, a, u);
    let start = cadd(d, p, a_u, n_av);

    let na_nv = cadd(d, p, na, nv);
    let s1 = cadd(d, p, a_u, na_nv);
    let h1 = {
        let refl_au = erefl(d, p, a_u);
        let nd = neg_add(d, p, a, v);
        d.lemma(p.add_congr, &[a_u, a_u, n_av, na_nv, refl_au, nd])
    };

    let (target2, h2) = add4_comm(d, p, a, u, na, nv);

    let zero_c = czero(d, p);
    let a_na = cadd(d, p, a, na);
    let u_nv = cadd(d, p, u, nv);
    let s3 = cadd(d, p, zero_c, u_nv);
    let h3 = {
        let hn = d.lemma(p.add_neg, &[a]);
        let refl_unv = erefl(d, p, u_nv);
        d.lemma(p.add_congr, &[a_na, zero_c, u_nv, u_nv, hn, refl_unv])
    };

    let unv_zero = cadd(d, p, u_nv, zero_c);
    let h4 = {
        let comm = d.lemma(p.add_comm, &[zero_c, u_nv]);
        let z = d.lemma(p.add_zero, &[u_nv]);
        d.lemma(p.equiv_trans, &[s3, unv_zero, u_nv, comm, z])
    };

    echain(
        d,
        p,
        start,
        &[(s1, h1), (target2, h2), (s3, h3), (u_nv, h4)],
    )
}

/// From `h : close_within u v q`, derive `close_within (add a u) (add a v) q`.
fn close_within_shift(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    u: ExprId,
    v: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let cancel = shift_diff_cancel(d, p, a, u, v);
    let a_u = cadd(d, p, a, u);
    let a_v = cadd(d, p, a, v);
    let neg_a_v = cneg(d, p, a_v);
    let diff_shifted = cadd(d, p, a_u, neg_a_v);
    let neg_v = cneg(d, p, v);
    let diff_plain = cadd(d, p, u, neg_v);
    let ac = d.lemma(p.abs_congr, &[diff_shifted, diff_plain, cancel]);
    let abs_shifted = cabs(d, p, diff_shifted);
    let abs_plain = cabs(d, p, diff_plain);
    let ac_rev = esymm(d, p, abs_shifted, abs_plain, ac);
    let refl_q = erefl(d, p, q);
    d.lemma(
        p.le_congr,
        &[abs_plain, abs_shifted, q, q, ac_rev, refl_q, h],
    )
}

/// From `h : Rat.le u (radd v q)`, derive
/// `CReal.le (ofRat u) (add (ofRat v) (ofRat q))`.
fn of_rat_le_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let rat = p.rat;
    let vq = radd(d, v, q);
    let raw = d.lemma(p.of_rat_le, &[u, vq, h]);
    let add_eq = d.lemma(p.of_rat_add, &[v, q]);
    let ov = d.const_app(p.of_rat, &[v]);
    let oq = d.const_app(p.of_rat, &[q]);
    let ovq_sum = cadd(d, p, ov, oq);
    let ovq_embed = d.const_app(p.of_rat, &[vq]);
    let add_eq_rev = esymm(d, p, ovq_sum, ovq_embed, add_eq);
    let ou = d.const_app(p.of_rat, &[u]);
    let refl_ou = erefl(d, p, ou);
    let _ = rat;
    d.lemma(
        p.le_congr,
        &[ou, ou, ovq_embed, ovq_sum, refl_ou, add_eq_rev, raw],
    )
}

/// `le (abs x) (mag_bound (bound x))` -- unconditional, for ANY `CReal`.
/// Via `CReal.bound_within`, read pointwise at a symbolic sample index (the
/// same "unfold `le`, work in `Rat`, re-`lam_fv`" idiom
/// [`declare_bucket_clamp_upper`]/[`declare_sample_upper_bound`] already use
/// to introduce a fresh `CReal.le` fact).
fn abs_bound_of_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let rat = p.rat;
    let nat_ty = d.nat_ty();
    let bx = ubound_of(d, p, x);
    let bval = bound_value(d, p, x);
    let zero_rat = rzero(d, rat);
    let two_nat = d.num(2);

    let le_upper_full = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let xn = sample(d, p, x, n);
        let bw = d.lemma(p.bound_within, &[x, n]);
        let (_, bw_upper) = halves(d, p, xn, bval, bw);
        let bval_z = radd(d, bval, zero_rat);
        let add_zero_eq = d.lemma(rat.add_zero, &[bval]);
        let eq_rev = rsymm(d, bval_z, bval, add_zero_eq);
        let xn_le_bvalz = rat_eq_rewrite(d, bval, bval_z, eq_rev, bw_upper, &|d, t| {
            rle(d, rat, xn, t)
        });
        let sub_le = d.lemma(rat.sub_le_of_le, &[xn, bval, zero_rat, xn_le_bvalz]);
        let bound2n = div_succ(d, p, 2, n);
        let zero_le_2n = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, n]);
        let sub_xn_bval = rsub(d, rat, xn, bval);
        let at_n = d.lemma(
            rat.le_trans,
            &[sub_xn_bval, zero_rat, bound2n, sub_le, zero_le_2n],
        );
        d.lam_fv(n_fv, nat_ty, at_n)
    };

    let le_lower_raw = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let xn = sample(d, p, x, n);
        let bw = d.lemma(p.bound_within, &[x, n]);
        let (bw_lower, _) = halves(d, p, xn, bval, bw);
        let neg_bval = rneg(d, bval);
        let xn_z = radd(d, xn, zero_rat);
        let add_zero_eq = d.lemma(rat.add_zero, &[xn]);
        let eq_rev = rsymm(d, xn_z, xn, add_zero_eq);
        let negbval_le_xnz = rat_eq_rewrite(d, xn, xn_z, eq_rev, bw_lower, &|d, t| {
            rle(d, rat, neg_bval, t)
        });
        let sub_le = d.lemma(rat.sub_le_of_le, &[neg_bval, xn, zero_rat, negbval_le_xnz]);
        let bound2n = div_succ(d, p, 2, n);
        let zero_le_2n = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, n]);
        let sub_expr = rsub(d, rat, neg_bval, xn);
        let at_n = d.lemma(
            rat.le_trans,
            &[sub_expr, zero_rat, bound2n, sub_le, zero_le_2n],
        );
        d.lam_fv(n_fv, nat_ty, at_n)
    };

    let mbx = mag_bound(d, p, bx);
    let neg_mbx = cneg(d, p, mbx);
    let step1 = d.lemma(p.neg_le_neg, &[neg_mbx, x, le_lower_raw]);
    let dn = double_neg(d, p, mbx);
    let neg_x = cneg(d, p, x);
    let refl_negx = erefl(d, p, neg_x);
    let n_mbx = cneg(d, p, mbx);
    let nn_mbx = cneg(d, p, n_mbx);
    let h2 = d.lemma(
        p.le_congr,
        &[neg_x, neg_x, nn_mbx, mbx, refl_negx, dn, step1],
    );
    d.lemma(p.abs_le, &[x, mbx, le_upper_full, h2])
}

/// Admit [`CRealPrelude::abs_bound_of_self`] — `∀ x, le (abs x) (mag_bound
/// (bound x))`. Promotes the private [`abs_bound_of_self`] helper (which
/// already builds this proof at an arbitrary `x`, including a free
/// variable) to a universally-quantified `CRealPrelude` field, by running it
/// once at a fresh `fvar` and `pi_fv`/`lam_fv`-closing the result — the same
/// "prove at an fvar, then bind" idiom every other lemma in this module
/// uses.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_abs_bound_of_self(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let body = abs_bound_of_self(d, p, x);
    let bx = ubound_of(d, p, x);
    let mbx = mag_bound(d, p, bx);
    let abs_x = cabs(d, p, x);
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = {
        let concl = d.const_app(p.le, &[abs_x, mbx]);
        d.pi_fv(x_fv, carrier, concl)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.abs_bound_of_self,
        uparams: vec![],
        ty,
        value,
    })
}

/// `gp(i) := Rat.min (natDivSucc i k) cap`.
fn gp_rat(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, cap: ExprId, i: ExprId) -> ExprId {
    let raw_i = div_succ_at(d, p, i, k);
    d.const_app(p.rat.min, &[raw_i, cap])
}

/// `Rat.le Rat.zero (gp i)`.
fn gp_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    cap: ExprId,
    i: ExprId,
    cap_nonneg: ExprId,
) -> ExprId {
    let rat = p.rat;
    let raw_i = div_succ_at(d, p, i, k);
    let raw_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[i, k]);
    let zero_rat = rzero(d, rat);
    d.lemma(rat.le_min, &[raw_i, cap, zero_rat, raw_nonneg, cap_nonneg])
}

/// `Rat.le (gp i) cap`.
fn gp_le_cap(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, cap: ExprId, i: ExprId) -> ExprId {
    let raw_i = div_succ_at(d, p, i, k);
    d.lemma(p.rat.min_le_right, &[raw_i, cap])
}

/// `Rat.le (gp i) (gp (succ i))`.
fn gp_mono(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, cap: ExprId, i: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let raw_i = div_succ_at(d, p, i, k);
    let succ_i = d.succ(i);
    let raw_si = div_succ_at(d, p, succ_i, k);
    let gp_i = d.const_app(rat.min, &[raw_i, cap]);
    let gp_i_le_raw_i = d.lemma(rat.min_le_left, &[raw_i, cap]);
    let raw_mono = d.lemma(rat.nat_div_succ_le_add_left, &[i, one_nat, k]);
    let gp_i_le_raw_si = d.lemma(
        rat.le_trans,
        &[gp_i, raw_i, raw_si, gp_i_le_raw_i, raw_mono],
    );
    let gp_i_le_cap = d.lemma(rat.min_le_right, &[raw_i, cap]);
    d.lemma(
        rat.le_min,
        &[raw_si, cap, gp_i, gp_i_le_raw_si, gp_i_le_cap],
    )
}

/// `Rat.le (sub (gp (succ i)) (gp i)) delta`, `delta := natDivSucc 1 k`.
fn gp_diff_upper(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, cap: ExprId, i: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let raw_i = div_succ_at(d, p, i, k);
    let succ_i = d.succ(i);
    let raw_si = div_succ_at(d, p, succ_i, k);
    let delta = div_succ(d, p, 1, k);

    let h1 = {
        let sum = radd(d, raw_i, delta);
        let eq1 = d.lemma(rat.nat_div_succ_add, &[i, one_nat, k]);
        // eq1 : Eq sum raw_si  (up to `add i one` ~ `succ i` defeq)
        let eq1_rev = rsymm(d, sum, raw_si, eq1);
        let refl_raw_si = d.lemma(rat.le_refl, &[raw_si]);
        let raw_si_le_sum = rat_eq_rewrite(d, raw_si, sum, eq1_rev, refl_raw_si, &|d, t| {
            rle(d, rat, raw_si, t)
        });
        d.lemma(rat.sub_le_of_le, &[raw_si, raw_i, delta, raw_si_le_sum])
    };
    let h2 = {
        let sub_cap_cap = rsub(d, rat, cap, cap);
        let sub_self_eq = d.lemma(rat.sub_self, &[cap]);
        let zero_rat = rzero(d, rat);
        let zero_le_delta = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, k]);
        let eq_rev = rsymm(d, sub_cap_cap, zero_rat, sub_self_eq);
        rat_eq_rewrite(d, zero_rat, sub_cap_cap, eq_rev, zero_le_delta, &|d, t| {
            rle(d, rat, t, delta)
        })
    };
    d.lemma(rat.sub_min_le, &[raw_si, cap, raw_i, cap, delta, h1, h2])
}

/// `Rat.le (sub (gp i) (gp (succ i))) delta`.
fn gp_diff_lower(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, cap: ExprId, i: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let delta = div_succ(d, p, 1, k);
    let gpm = gp_mono(d, p, k, cap, i);
    let gp_i = gp_rat(d, p, k, cap, i);
    let succ_i = d.succ(i);
    let gp_si = gp_rat(d, p, k, cap, succ_i);
    let delta_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, k]);
    let refl_gpsi = d.lemma(rat.le_refl, &[gp_si]);
    let zero_rat = rzero(d, rat);
    let widen = d.lemma(
        rat.add_le_add,
        &[gp_si, gp_si, zero_rat, delta, refl_gpsi, delta_nonneg],
    );
    let gpsi_z = radd(d, gp_si, zero_rat);
    let add_zero_eq = d.lemma(rat.add_zero, &[gp_si]);
    let target = radd(d, gp_si, delta);
    let step = rat_eq_rewrite(d, gpsi_z, gp_si, add_zero_eq, widen, &|d, t| {
        rle(d, rat, t, target)
    });
    let chained = d.lemma(rat.le_trans, &[gp_i, gp_si, target, gpm, step]);
    d.lemma(rat.sub_le_of_le, &[gp_i, gp_si, delta, chained])
}

/// `Rat.le (natDivSucc 1 k) (natDivSucc 1 m0)`.
fn delta_le_delta_uc(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, m0: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let three_nat = d.num(3);
    let delta = div_succ(d, p, 1, k);
    let d3k = div_succ(d, p, 3, k);
    let refl_delta = d.lemma(rat.le_refl, &[delta]);
    let d3k_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[three_nat, k]);
    let zero_rat = rzero(d, rat);
    let widen1 = d.lemma(
        rat.add_le_add,
        &[delta, delta, zero_rat, d3k, refl_delta, d3k_nonneg],
    );
    let delta_z = radd(d, delta, zero_rat);
    let add_zero_eq = d.lemma(rat.add_zero, &[delta]);
    let sum = radd(d, delta, d3k);
    let step0 = rat_eq_rewrite(d, delta_z, delta, add_zero_eq, widen1, &|d, t| {
        rle(d, rat, t, sum)
    });
    // step0 : le delta sum,  sum = add delta d3k
    let eq4 = d.lemma(rat.nat_div_succ_add, &[one_nat, three_nat, k]);
    let four_nat = d.num(4);
    let four_k = div_succ_at(d, p, four_nat, k);
    let step1 = rat_eq_rewrite(d, sum, four_k, eq4, step0, &|d, t| rle(d, rat, delta, t));
    let scale = d.lemma(rat.nat_div_succ_scale, &[three_nat, m0]);
    let deltauc = div_succ(d, p, 1, m0);
    rat_eq_rewrite(d, four_k, deltauc, scale, step1, &|d, t| {
        rle(d, rat, delta, t)
    })
}

/// `Nat.le k j`, `j := (succ k)*(succ k)`.
fn k_le_j(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let nat_p = p.rat.int.nat;
    let k1 = d.succ(k);
    let j = NatOps::mul(d, k1, k1);
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let k_le_k1 = d.lemma(nat_p.le_succ, &[k]);
    let zero_le_k = d.lemma(nat_p.zero_le, &[k]);
    let one_le_k1 = d.lemma(nat_p.succ_le_succ, &[zero_nat, k, zero_le_k]);
    let mul_mono = d.lemma(nat_p.mul_le_mul_left, &[k1, one_nat, k1, one_le_k1]);
    let mul_one_eq = d.lemma(nat_p.mul_one, &[k1]);
    let mul_k1_1 = NatOps::mul(d, k1, one_nat);
    let k1_le_j = nat_rewrite_prop(d, mul_k1_1, k1, mul_one_eq, mul_mono, &|d, t| {
        NatOps::le(d, t, j)
    });
    d.lemma(nat_p.le_trans, &[k, k1, j, k_le_k1, k1_le_j])
}

/// `Eq (add (add (natDivSucc 1 x) (natDivSucc 1 x)) (natDivSucc 1 x))
/// (natDivSucc 3 x)`. Returns `(sum_expr, proof)`.
fn nat_div_succ_three_fuse(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);
    let d1 = div_succ_at(d, p, one_nat, x);
    let sum2 = radd(d, d1, d1);
    let eq1 = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, x]);
    let d2 = div_succ_at(d, p, two_nat, x);
    let sum3 = radd(d, sum2, d1);
    let cong = rcongr(d, sum2, d2, eq1, &|d, t| radd(d, t, d1));
    let sum3b = radd(d, d2, d1);
    let eq2 = d.lemma(rat.nat_div_succ_add, &[two_nat, one_nat, x]);
    let d3 = div_succ_at(d, p, three_nat, x);
    let (_, chained) = rchain(d, sum3, &[(sum3b, cong), (d3, eq2)]);
    (sum3, chained)
}

/// `Rat.le (natDivSucc 3 j) (natDivSucc 3 k)`, from `Nat.le k j`.
fn nat_div_succ3_antitone(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    j: ExprId,
    hkj: ExprId,
) -> ExprId {
    let rat = p.rat;
    let d1j = div_succ(d, p, 1, j);
    let d1k = div_succ(d, p, 1, k);
    let a1 = d.lemma(rat.nat_div_succ_antitone, &[k, j, hkj]);
    let two_le = d.lemma(rat.add_le_add, &[d1j, d1k, d1j, d1k, a1, a1]);
    let sum2j = radd(d, d1j, d1j);
    let sum2k = radd(d, d1k, d1k);
    let three_le = d.lemma(rat.add_le_add, &[sum2j, sum2k, d1j, d1k, two_le, a1]);
    let (sum3j, eqj) = nat_div_succ_three_fuse(d, p, j);
    let (sum3k, eqk) = nat_div_succ_three_fuse(d, p, k);
    let d3j = div_succ(d, p, 3, j);
    let d3k = div_succ(d, p, 3, k);
    let step1 = rat_eq_rewrite(d, sum3j, d3j, eqj, three_le, &|d, t| rle(d, rat, t, sum3k));
    rat_eq_rewrite(d, sum3k, d3k, eqk, step1, &|d, t| rle(d, rat, d3j, t))
}

/// `Rat.le (add (natDivSucc 1 k) (natDivSucc 3 j)) (natDivSucc 1 m0)`.
fn e_le_delta_uc(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    m0: ExprId,
    j: ExprId,
    hkj: ExprId,
) -> ExprId {
    let rat = p.rat;
    let delta = div_succ(d, p, 1, k);
    let d3j = div_succ(d, p, 3, j);
    let d3k = div_succ(d, p, 3, k);
    let step_jk = nat_div_succ3_antitone(d, p, k, j, hkj);
    let refl_delta = d.lemma(rat.le_refl, &[delta]);
    let widen1 = d.lemma(
        rat.add_le_add,
        &[delta, delta, d3j, d3k, refl_delta, step_jk],
    );
    let e_expr = radd(d, delta, d3j);
    let sum_dk = radd(d, delta, d3k);
    let one_nat = d.num(1);
    let three_nat = d.num(3);
    let eq4 = d.lemma(rat.nat_div_succ_add, &[one_nat, three_nat, k]);
    let four_nat = d.num(4);
    let four_k = div_succ_at(d, p, four_nat, k);
    let step2 = rat_eq_rewrite(d, sum_dk, four_k, eq4, widen1, &|d, t| {
        rle(d, rat, e_expr, t)
    });
    let scale = d.lemma(rat.nat_div_succ_scale, &[three_nat, m0]);
    let deltauc = div_succ(d, p, 1, m0);
    rat_eq_rewrite(d, four_k, deltauc, scale, step2, &|d, t| {
        rle(d, rat, e_expr, t)
    })
}

/// `Rat.le b (radd a b)`, from `ha : Rat.le Rat.zero a`.
fn rat_le_add_left_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_rat = rzero(d, rat);
    let refl_b = d.lemma(rat.le_refl, &[b]);
    let widen = d.lemma(rat.add_le_add, &[zero_rat, a, b, b, ha, refl_b]);
    let zero_b = radd(d, zero_rat, b);
    let comm = d.lemma(rat.add_comm, &[zero_rat, b]);
    let b_z = radd(d, b, zero_rat);
    let az = d.lemma(rat.add_zero, &[b]);
    let (_, chain_eq) = rchain(d, zero_b, &[(b_z, comm), (b, az)]);
    let target = radd(d, a, b);
    rat_eq_rewrite(d, zero_b, b, chain_eq, widen, &|d, t| {
        rle(d, rat, t, target)
    })
}

/// From `h : le x (ofRat (radd v q))`, derive `le x (add (ofRat v) (ofRat q))`.
fn creal_le_ofrat_add_of_le_ofrat_sum(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    v: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let vq = radd(d, v, q);
    let add_eq = d.lemma(p.of_rat_add, &[v, q]);
    let ov = d.const_app(p.of_rat, &[v]);
    let oq = d.const_app(p.of_rat, &[q]);
    let sum = cadd(d, p, ov, oq);
    let ovq = d.const_app(p.of_rat, &[vq]);
    let add_eq_rev = esymm(d, p, sum, ovq, add_eq);
    let refl_x = erefl(d, p, x);
    d.lemma(p.le_congr, &[x, x, ovq, sum, refl_x, add_eq_rev, h])
}

/// From `heq : Equiv x x2` and `h : close_within x y q`, derive
/// `close_within x2 y q`.
fn close_within_congr_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    x2: ExprId,
    y: ExprId,
    q: ExprId,
    heq: ExprId,
    h: ExprId,
) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let diff2 = cadd(d, p, x2, ny);
    let refl_ny = erefl(d, p, ny);
    let dc = d.lemma(p.add_congr, &[x, x2, ny, ny, heq, refl_ny]);
    let ac = d.lemma(p.abs_congr, &[diff, diff2, dc]);
    let refl_q = erefl(d, p, q);
    let abs_diff = cabs(d, p, diff);
    let abs_diff2 = cabs(d, p, diff2);
    d.lemma(p.le_congr, &[abs_diff, abs_diff2, q, q, ac, refl_q, h])
}

/// From `hprev : le (abs prev) qprev` and
/// `herr : le (abs (add cur (neg prev))) qerr` (i.e. `close_within cur prev
/// qerr`), derive `le (abs cur) (add qprev qerr)`.
fn triangle_step(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    prev: ExprId,
    cur: ExprId,
    qprev: ExprId,
    qerr: ExprId,
    hprev: ExprId,
    herr: ExprId,
) -> ExprId {
    let nprev = cneg(d, p, prev);
    let sub_cur_prev = cadd(d, p, cur, nprev);
    // cancel_id : Equiv sum_pc cur  (`add_sub_cancel(prev, cur)`, `a + (b-a) ~ b`)
    let cancel_id = add_sub_cancel(d, p, prev, cur);
    let sum_pc = cadd(d, p, prev, sub_cur_prev);
    let abs_cur = cabs(d, p, cur);
    let abs_sum = cabs(d, p, sum_pc);
    // ac : Equiv abs_sum abs_cur
    let ac = d.lemma(p.abs_congr, &[sum_pc, cur, cancel_id]);
    // triangle : le abs_sum target
    let triangle = d.lemma(p.abs_add_le, &[prev, sub_cur_prev]);
    let abs_prev = cabs(d, p, prev);
    let abs_sub = cabs(d, p, sub_cur_prev);
    let target = cadd(d, p, abs_prev, abs_sub);
    let refl_target = erefl(d, p, target);
    // step1 : le abs_cur target
    let step1 = d.lemma(
        p.le_congr,
        &[abs_sum, abs_cur, target, target, ac, refl_target, triangle],
    );
    let sum_bound = cadd(d, p, qprev, qerr);
    let combine = d.lemma(p.add_le_add, &[abs_prev, qprev, abs_sub, qerr, hprev, herr]);
    d.lemma(p.le_trans, &[abs_cur, target, sum_bound, step1, combine])
}

/// `CReal.bucketClose : ∀ (bnd : CReal) (m0 : Nat) (cap : Rat), Rat.le
/// (Rat.sub (CReal.seq bnd j) (Rat.natDivSucc 1 j)) cap → ∀ (w : CReal),
/// CReal.le CReal.zero w → CReal.le w bnd → CReal.le (CReal.abs (CReal.add w
/// (CReal.neg (CReal.ofRat (Rat.min (Rat.natDivSucc (CReal.bucketIndex w k)
/// k) cap))))) (CReal.ofRat (Rat.natDivSucc 1 m0))` -- `k :=
/// rescale_index(3, m0) = 4*m0+3`, `j := (Nat.succ k) * (Nat.succ k)`.
///
/// The "`w` is close to its own clamped grid-point sample, at target
/// accuracy `m0`" fact from Spivak ch.7's covering argument (see
/// [`declare_bounded_of_uniformly_continuous`]'s own doc comment for the
/// whole argument this is one piece of): `w`'s clamped grid point
/// `GP(bucketIndex(w,k)) := min(natDivSucc(bucketIndex(w,k), k), cap)`
/// lands within `1/(m0+1)` of `w`. `m0` is supplied by the caller (in the
/// covering argument, `uc_modulus` read at accuracy 0) as an opaque `Nat`;
/// `cap` is any clamp bound satisfying the hypothesis above
/// (`bounded_of_uniformly_continuous` instantiates it at
/// `max(seq bnd j - natDivSucc 1 j, 0)`, but nothing below depends on that
/// particular choice). Nothing here is specific to a uniformly-continuous
/// function or its interval -- `bnd`, `cap`, `w` are all arbitrary.
///
/// `k` is `rescale_index(3, m0)`, NOT an independent `Nat` parameter, even
/// though nothing else in this statement forces that relationship: the
/// widening from `e_expr` down to `natDivSucc 1 m0` goes through
/// `Rat.natDivSucc_scale`, whose conclusion is stated at EXACTLY
/// `rescale_index(3, m0)`, not merely at some index `>= ` it. An earlier
/// version of this extraction took `k` as its own free `Nat` parameter; the
/// kernel correctly REJECTED it with a `TypeMismatch` between `natDivSucc 4
/// k` (a bare fvar) and `natDivSucc 4 (rescale_index 3 m0)` (what
/// `nat_div_succ_scale` actually proves) -- the two are related only once
/// `k` is pinned to that exact value, which is why `k` is derived here
/// rather than bound.
///
/// Extracted from `declare_bounded_of_uniformly_continuous`, which used to
/// assemble exactly this fact INLINE, behind five private helpers
/// ([`clamp_setup`], [`k_le_j`], [`creal_le_of_sub_le`],
/// [`rat_le_add_left_of_nonneg`], [`creal_le_ofrat_add_of_le_ofrat_sum`]) --
/// structurally invisible to both grep and `shape_search`, since an inline
/// step has no declaration to index (CLAUDE.md's "hiding place 2").
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_bucket_close(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat_ty_top = rat_ty(d);
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    // `k` is NOT independent of `m0` -- it is derived as
    // `rescale_index(3, m0)` (matching `declare_bounded_of_uniformly_continuous`'s
    // own construction), because the widening from `e_expr` down to
    // `natDivSucc 1 m0` at the end of this proof goes through
    // `Rat.natDivSucc_scale`, whose conclusion is stated at EXACTLY
    // `rescale_index(3, m0)`, not at an arbitrary index merely `>=` it. An
    // earlier version of this extraction took `k` as its own free `Nat`
    // parameter, unrelated to `m0`; the kernel correctly REJECTED it with a
    // `TypeMismatch` between `natDivSucc 4 k` (a bare fvar) and `natDivSucc 4
    // (rescale_index(3, m0))` (what `nat_div_succ_scale` actually proves) --
    // the two are propositionally related only once `k` is pinned to that
    // exact value.
    let bnd_fv = d.fresh_fvar();
    let bnd = d.kernel().fvar(bnd_fv);
    let m0_fv = d.fresh_fvar();
    let m0 = d.kernel().fvar(m0_fv);
    let three_nat = d.num(3);
    let k = rescale_index(d, three_nat, m0);
    let cap_fv = d.fresh_fvar();
    let cap = d.kernel().fvar(cap_fv);

    let k1 = d.succ(k);
    let j = NatOps::mul(d, k1, k1);
    let bnd_j_ty_probe = sample(d, p, bnd, j);
    let nds1j_ty_probe = div_succ(d, p, 1, j);
    let raw_ty_probe = rsub(d, rat, bnd_j_ty_probe, nds1j_ty_probe);
    let cap_le_raw_side_ty = rle(d, rat, raw_ty_probe, cap);
    let cap_le_raw_side_fv = d.fresh_fvar();
    let cap_le_raw_side = d.kernel().fvar(cap_le_raw_side_fv);

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let h0w_ty = {
        let zero_c = czero(d, p);
        d.const_app(p.le, &[zero_c, w])
    };
    let h0w_fv = d.fresh_fvar();
    let h0w = d.kernel().fvar(h0w_fv);
    let hle_ty = d.const_app(p.le, &[w, bnd]);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let m = d.const_app(p.bucket_index, &[w, k]);
    let deltauc = div_succ(d, p, 1, m0);
    let odeltauc = d.const_app(p.of_rat, &[deltauc]);

    // --- body, identical to `declare_bounded_of_uniformly_continuous`'s own
    // former inline "z close to GP(m)" step (now called from there instead
    // of duplicated). -----------------------------------------------------
    let (jw, _wj, qw) = clamp_setup(d, p, w, k);
    let _ = jw;
    let raw_m = div_succ_at(d, p, m, k);
    let succ_m = d.succ(m);
    let raw_sm = div_succ_at(d, p, succ_m, k);
    let delta = div_succ(d, p, 1, k);
    let nds1j = div_succ(d, p, 1, j);
    let nds2j = div_succ(d, p, 2, j);
    let nds3j = div_succ(d, p, 3, j);
    let e_expr = radd(d, delta, nds3j);
    let oe = d.const_app(p.of_rat, &[e_expr]);

    let floor_lower = d.lemma(p.bucket_index_floor_lower, &[w, k]);
    let floor_upper = d.lemma(p.bucket_index_floor_upper, &[w, k]);
    let clamp_up = d.lemma(p.bucket_clamp_upper, &[w, k]);
    let clamp_lo = d.lemma(p.bucket_clamp_lower, &[w, k, h0w]);

    // shared: `ofRat q_w <= add w (ofRat nds3j)`.
    let oqw = d.const_app(p.of_rat, &[qw]);
    let onds3j = d.const_app(p.of_rat, &[nds3j]);
    let qw_le_w_plus = {
        let of_rat_sub_eq = d.lemma(p.of_rat_sub, &[qw, nds3j]);
        // of_rat_sub_eq : Equiv (add oqw (neg onds3j)) (ofRat (rsub qw nds3j))
        let neg_onds3j = cneg(d, p, onds3j);
        let diff_form = cadd(d, p, oqw, neg_onds3j);
        let qw_minus_nds3j = rsub(d, rat, qw, nds3j);
        let sub_embed = d.const_app(p.of_rat, &[qw_minus_nds3j]);
        let of_rat_sub_eq_rev = esymm(d, p, diff_form, sub_embed, of_rat_sub_eq);
        let refl_w2 = erefl(d, p, w);
        let clamp_lo2 = d.lemma(
            p.le_congr,
            &[
                sub_embed,
                diff_form,
                w,
                w,
                of_rat_sub_eq_rev,
                refl_w2,
                clamp_lo,
            ],
        );
        // clamp_lo2 : le diff_form w = le (add oqw (neg onds3j)) w
        let raw = creal_le_of_sub_le(d, p, oqw, onds3j, w, clamp_lo2);
        // raw : le oqw (add onds3j w)
        let onds3j_w = cadd(d, p, onds3j, w);
        let w_onds3j = cadd(d, p, w, onds3j);
        let comm = d.lemma(p.add_comm, &[onds3j, w]);
        let refl_oqw = erefl(d, p, oqw);
        d.lemma(
            p.le_congr,
            &[oqw, oqw, onds3j_w, w_onds3j, refl_oqw, comm, raw],
        )
        // : le oqw (add w onds3j)
    };
    let delta_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, k]);
    let nds3j_le_e = rat_le_add_left_of_nonneg(d, p, delta, nds3j, delta_nonneg);

    let hkj = k_le_j(d, p, k);
    let e_le_deltauc = e_le_delta_uc(d, p, k, m0, j, hkj);

    let z_close_predicate = {
        let rat_ty_e2 = rat_ty(d);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ot = d.const_app(p.of_rat, &[t]);
        let body_ty = close_of_bounds_ty(d, p, w, ot, oe);
        d.lam_fv(t_fv, rat_ty_e2, body_ty)
    };
    let on_le_branch = {
        let h_fv = d.fresh_fvar();
        let _hle_branch = d.kernel().fvar(h_fv);
        let hyp_ty = rle(d, rat, raw_m, cap);

        let h1 = {
            let eq_sm = d.lemma(rat.nat_div_succ_add, &[m, one_nat, k]);
            let sum_m_delta = radd(d, raw_m, delta);
            let eq_sm_rev = rsymm(d, sum_m_delta, raw_sm, eq_sm);
            let qw_le_summdelta =
                rat_eq_rewrite(d, raw_sm, sum_m_delta, eq_sm_rev, floor_upper, &|d, t| {
                    rle(d, rat, qw, t)
                });
            let refl_nds2j = d.lemma(rat.le_refl, &[nds2j]);
            let widen0 = d.lemma(
                rat.add_le_add,
                &[qw, sum_m_delta, nds2j, nds2j, qw_le_summdelta, refl_nds2j],
            );
            let assoc = d.lemma(rat.add_assoc, &[raw_m, delta, nds2j]);
            let sum_m_delta_nds2j = radd(d, sum_m_delta, nds2j);
            let raw_m_dn = radd(d, delta, nds2j);
            let raw_m_plus_dn = radd(d, raw_m, raw_m_dn);
            let qw_nds2j = radd(d, qw, nds2j);
            let step1 = rat_eq_rewrite(
                d,
                sum_m_delta_nds2j,
                raw_m_plus_dn,
                assoc,
                widen0,
                &|d, t| rle(d, rat, qw_nds2j, t),
            );
            let mono23 = d.lemma(rat.nat_div_succ_le_add_left, &[two_nat, one_nat, j]);
            let refl_delta2 = d.lemma(rat.le_refl, &[delta]);
            let widen1 = d.lemma(
                rat.add_le_add,
                &[delta, delta, nds2j, nds3j, refl_delta2, mono23],
            );
            let refl_rawm = d.lemma(rat.le_refl, &[raw_m]);
            let raw_m_plus_e = radd(d, raw_m, e_expr);
            let widen2 = d.lemma(
                rat.add_le_add,
                &[raw_m, raw_m, raw_m_dn, e_expr, refl_rawm, widen1],
            );
            let step2 = d.lemma(
                rat.le_trans,
                &[qw_nds2j, raw_m_plus_dn, raw_m_plus_e, step1, widen2],
            );
            let ofrat_step2 = d.lemma(p.of_rat_le, &[qw_nds2j, raw_m_plus_e, step2]);
            let o_qw_nds2j = d.const_app(p.of_rat, &[qw_nds2j]);
            let o_raw_m_plus_e = d.const_app(p.of_rat, &[raw_m_plus_e]);
            let w_le = d.lemma(
                p.le_trans,
                &[w, o_qw_nds2j, o_raw_m_plus_e, clamp_up, ofrat_step2],
            );
            creal_le_ofrat_add_of_le_ofrat_sum(d, p, w, raw_m, e_expr, w_le)
        };
        let h2 = {
            let ofrat_le = d.lemma(p.of_rat_le, &[raw_m, qw, floor_lower]);
            let onds3j2 = d.const_app(p.of_rat, &[nds3j]);
            let orawm = d.const_app(p.of_rat, &[raw_m]);
            let w_plus_nds3j = cadd(d, p, w, onds3j2);
            let step1 = d.lemma(
                p.le_trans,
                &[orawm, oqw, w_plus_nds3j, ofrat_le, qw_le_w_plus],
            );
            let widen_final = d.lemma(p.of_rat_le, &[nds3j, e_expr, nds3j_le_e]);
            let refl_w3 = d.lemma(p.le_refl, &[w]);
            let step2 = d.lemma(p.add_le_add, &[w, w, onds3j2, oe, refl_w3, widen_final]);
            let w_plus_oe = cadd(d, p, w, oe);
            d.lemma(p.le_trans, &[orawm, w_plus_nds3j, w_plus_oe, step1, step2])
        };
        let ot_rm = d.const_app(p.of_rat, &[raw_m]);
        let closeval = close_of_bounds(d, p, w, ot_rm, oe, h1, h2);
        d.lam_fv(h_fv, hyp_ty, closeval)
    };
    let on_ge_branch = {
        let h_fv = d.fresh_fvar();
        let hge_branch = d.kernel().fvar(h_fv);
        let hyp_ty = rle(d, rat, cap, raw_m);
        let ot_cap = d.const_app(p.of_rat, &[cap]);

        let h1 = {
            let bnd_j = sample(d, p, bnd, j);
            let sample_ub = d.lemma(p.sample_upper_bound, &[bnd, j]);
            // sample_ub : le bnd (ofRat (radd (seq bnd j) (natDivSucc 1 j)))
            let bndj_nds1j = radd(d, bnd_j, nds1j);
            let o_bndj_nds1j = d.const_app(p.of_rat, &[bndj_nds1j]);
            let w_le_bnd = d.lemma(p.le_trans, &[w, bnd, o_bndj_nds1j, hle, sample_ub]);
            // seq(bnd,j) <= radd(nds1j,cap)
            let seq_le_cap_nds1j = d.lemma(rat.le_of_sub_le, &[bnd_j, nds1j, cap, cap_le_raw_side]);
            let refl_nds1j = d.lemma(rat.le_refl, &[nds1j]);
            let nds1j_cap = radd(d, nds1j, cap);
            let widen0 = d.lemma(
                rat.add_le_add,
                &[bnd_j, nds1j_cap, nds1j, nds1j, seq_le_cap_nds1j, refl_nds1j],
            );
            // widen0 : le (radd bnd_j nds1j) (radd (radd nds1j cap) nds1j)
            let target0 = radd(d, nds1j_cap, nds1j);
            let comm1 = d.lemma(rat.add_comm, &[nds1j, cap]);
            let cap_nds1j = radd(d, cap, nds1j);
            let step_c1 = rcongr(d, nds1j_cap, cap_nds1j, comm1, &|d, t| radd(d, t, nds1j));
            let target1 = radd(d, cap_nds1j, nds1j);
            let assoc1 = d.lemma(rat.add_assoc, &[cap, nds1j, nds1j]);
            let nds1j_nds1j = radd(d, nds1j, nds1j);
            let target2 = radd(d, cap, nds1j_nds1j);
            let (_, eq_target) = rchain(d, target0, &[(target1, step_c1), (target2, assoc1)]);
            let step1 = rat_eq_rewrite(d, target0, target2, eq_target, widen0, &|d, t| {
                rle(d, rat, bndj_nds1j, t)
            });
            // step1 : le (radd bnd_j nds1j) (radd cap nds1j_nds1j)
            let fuse2 = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, j]);
            // Eq nds1j_nds1j (natDivSucc (add 1 1) j) -- defeq nds2j
            let step2 = rat_eq_rewrite(d, nds1j_nds1j, nds2j, fuse2, step1, &|d, t| {
                let target = radd(d, cap, t);
                rle(d, rat, bndj_nds1j, target)
            });
            // step2 : le (radd bnd_j nds1j) (radd cap nds2j)
            let mono23 = d.lemma(rat.nat_div_succ_le_add_left, &[two_nat, one_nat, j]);
            let refl_cap = d.lemma(rat.le_refl, &[cap]);
            let widen1 = d.lemma(rat.add_le_add, &[cap, cap, nds2j, nds3j, refl_cap, mono23]);
            let cap_nds2j2 = radd(d, cap, nds2j);
            let cap_nds3j = radd(d, cap, nds3j);
            let step3 = d.lemma(
                rat.le_trans,
                &[bndj_nds1j, cap_nds2j2, cap_nds3j, step2, widen1],
            );
            let ofrat_step3 = d.lemma(p.of_rat_le, &[bndj_nds1j, cap_nds3j, step3]);
            let o_bndj_nds1j2 = d.const_app(p.of_rat, &[bndj_nds1j]);
            let o_cap_nds3j = d.const_app(p.of_rat, &[cap_nds3j]);
            let w_le2 = d.lemma(
                p.le_trans,
                &[w, o_bndj_nds1j2, o_cap_nds3j, w_le_bnd, ofrat_step3],
            );
            let h1_nds3j = creal_le_ofrat_add_of_le_ofrat_sum(d, p, w, cap, nds3j, w_le2);
            // h1_nds3j : le w (add ot_cap (ofRat nds3j))
            let widen_final1 = d.lemma(p.of_rat_le, &[nds3j, e_expr, nds3j_le_e]);
            let refl_cap3 = d.lemma(p.le_refl, &[ot_cap]);
            let onds3j4 = d.const_app(p.of_rat, &[nds3j]);
            let cap_plus_onds3j = cadd(d, p, ot_cap, onds3j4);
            let cap_plus_oe = cadd(d, p, ot_cap, oe);
            let step_final = d.lemma(
                p.add_le_add,
                &[ot_cap, ot_cap, onds3j4, oe, refl_cap3, widen_final1],
            );
            // step_final : le cap_plus_onds3j cap_plus_oe
            d.lemma(
                p.le_trans,
                &[w, cap_plus_onds3j, cap_plus_oe, h1_nds3j, step_final],
            )
        };
        let h2 = {
            let cap_le_qw = d.lemma(rat.le_trans, &[cap, raw_m, qw, hge_branch, floor_lower]);
            let ocap2 = d.const_app(p.of_rat, &[cap]);
            let onds3j3 = d.const_app(p.of_rat, &[nds3j]);
            let ofrat_le = d.lemma(p.of_rat_le, &[cap, qw, cap_le_qw]);
            let w_plus_nds3j = cadd(d, p, w, onds3j3);
            let step1 = d.lemma(
                p.le_trans,
                &[ocap2, oqw, w_plus_nds3j, ofrat_le, qw_le_w_plus],
            );
            let widen_final = d.lemma(p.of_rat_le, &[nds3j, e_expr, nds3j_le_e]);
            let refl_w4 = d.lemma(p.le_refl, &[w]);
            let step2 = d.lemma(p.add_le_add, &[w, w, onds3j3, oe, refl_w4, widen_final]);
            let w_plus_oe2 = cadd(d, p, w, oe);
            d.lemma(p.le_trans, &[ocap2, w_plus_nds3j, w_plus_oe2, step1, step2])
        };
        let closeval = close_of_bounds(d, p, w, ot_cap, oe, h1, h2);
        d.lam_fv(h_fv, hyp_ty, closeval)
    };
    let close_w_gpm_e = d.lemma(
        rat.min_cases,
        &[raw_m, cap, z_close_predicate, on_le_branch, on_ge_branch],
    );
    // close_w_gpm_e : close_within w (ofRat (gp_rat k cap m)) oe

    let widen_e = d.lemma(p.of_rat_le, &[e_expr, deltauc, e_le_deltauc]);
    let gpm_rat = gp_rat(d, p, k, cap, m);
    let ogpm = d.const_app(p.of_rat, &[gpm_rat]);
    let neg_ogpm = cneg(d, p, ogpm);
    let diff_w_gpm = cadd(d, p, w, neg_ogpm);
    let abs_w_gpm = cabs(d, p, diff_w_gpm);
    let close_w_gpm = d.lemma(
        p.le_trans,
        &[abs_w_gpm, oe, odeltauc, close_w_gpm_e, widen_e],
    );
    // close_w_gpm : close_within w (ofRat (gp_rat k cap m)) odeltauc

    let ty = {
        let concl = close_of_bounds_ty(d, p, w, ogpm, odeltauc);
        let with_hle = d.pi_fv(hle_fv, hle_ty, concl);
        let with_h0w = d.pi_fv(h0w_fv, h0w_ty, with_hle);
        let with_w = d.pi_fv(w_fv, carrier, with_h0w);
        let with_cap_le = d.pi_fv(cap_le_raw_side_fv, cap_le_raw_side_ty, with_w);
        let with_cap = d.pi_fv(cap_fv, rat_ty_top, with_cap_le);
        let with_m0 = d.pi_fv(m0_fv, nat, with_cap);
        d.pi_fv(bnd_fv, carrier, with_m0)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, close_w_gpm);
        let with_h0w = d.lam_fv(h0w_fv, h0w_ty, with_hle);
        let with_w = d.lam_fv(w_fv, carrier, with_h0w);
        let with_cap_le = d.lam_fv(cap_le_raw_side_fv, cap_le_raw_side_ty, with_w);
        let with_cap = d.lam_fv(cap_fv, rat_ty_top, with_cap_le);
        let with_m0 = d.lam_fv(m0_fv, nat, with_cap);
        d.lam_fv(bnd_fv, carrier, with_m0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bucket_close,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.bounded_of_uniformly_continuous : ∀ F a b, UniformlyContinuousOn F
/// a b → CReal.le a b → CReal.BoundedOn F a b K` for a COMPUTED `K` (never an
/// `Exists`-elimination: `Exists.rec` is `Prop`-only and `K` is used inside a
/// `Type`-free but still fully explicit Nat expression built from `F`, `a`,
/// `b`, `huc`, `hab` alone -- never from `z`, so it is one constant covering
/// the whole interval, which is the actual content of "bounded ON `[a,b]`"
/// as opposed to pointwise boundedness of every single `F z` (`CReal.bound`
/// already gives that, for free, with no continuity at all).
///
/// The covering argument (Spivak ch.7's proof, adapted to Bishop reals):
/// fix the uniform-continuity witness at accuracy `n = 0` (so consecutive
/// close points give a `mag_bound 0`-size output step), pick a grid
/// resolution `k := rescale_index 3 (modulus 0)` fine enough that three
/// units of the bucket-index floor slack plus one grid step still fits
/// inside `natDivSucc 1 (modulus 0)` exactly (`e_le_delta_uc`/
/// `delta_le_delta_uc`), and clamp every absolute grid point `i/(k+1)` down
/// to `cap` (a rational `≤ bnd := b − a`, from [`CRealPrelude::sample_lower_bound`]
/// applied to `bnd`) via `Rat.min` so `GP(i) := a + min(i/(k+1), cap)` is
/// unconditionally in `[a, b]` for every `i` (`gp_nonneg`/`gp_le_cap`, no
/// case split). An induction on `i` (`d.induct`) walks `|F(GP i)|` up from
/// `|F a|` (itself bounded by `CReal.bound`, [`abs_bound_of_self`]) one
/// `mag_bound 0` step per grid point (each step's own closeness comes from
/// `Rat.sub_min_le`'s one-Lipschitz property of `min`, [`gp_diff_upper`]/
/// [`gp_diff_lower`]), instantiated at `m := bucketIndex(z-a, k)` and widened
/// by [`CRealPrelude::bucket_index_bound`]'s uniform (`z`-free) cap `M` on
/// `m` via [`mag_bound_mono`]. The last step relates `z` itself to `GP(m)`:
/// `bucketIndexFloorLower`/`Upper` pin the clamped sample of `z-a` between
/// `GP(m)`'s two candidate values, and `Rat.min_cases` closes both branches
/// of which candidate `min` actually picked (the module documentation's
/// "rational clamp" fix) with the SAME slack `E := natDivSucc 1 k +
/// natDivSucc 3 j`, `j := (succ k)²` -- one more `mag_bound 0` step and one
/// more [`mag_bound_fuse_succ`] land the final bound.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_bounded_of_uniformly_continuous(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat_p = rat.int.nat;
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let huc_ty = uc_ty(d, p, f, a, b);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);

    let hab_ty = d.const_app(p.le, &[a, b]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);

    // --- fixed data (independent of `z`): the modulus at accuracy 0, the
    // grid resolution `k`, and the rational cap bounding `bnd`. -------------
    let modulus = d.const_app(p.uc_modulus, &[f, a, b, huc]);
    let spec = d.const_app(p.uc_spec, &[f, a, b, huc]);
    let m0 = d.apply(modulus, &[zero_nat]);
    let k = rescale_index(d, three_nat, m0);
    let k1 = d.succ(k);
    let j = NatOps::mul(d, k1, k1);
    let deltauc = div_succ(d, p, 1, m0);
    let odeltauc = d.const_app(p.of_rat, &[deltauc]);

    let na = cneg(d, p, a);
    let bnd = cadd(d, p, b, na);

    let hbnd0 = {
        let refl_na = d.lemma(p.le_refl, &[na]);
        let shifted = d.lemma(p.add_le_add, &[a, b, na, na, hab, refl_na]);
        let a_na = cadd(d, p, a, na);
        let zero_c = czero(d, p);
        let hn = d.lemma(p.add_neg, &[a]);
        let refl_bnd = erefl(d, p, bnd);
        d.lemma(p.le_congr, &[a_na, zero_c, bnd, bnd, hn, refl_bnd, shifted])
    };

    let raw = {
        let wj = sample(d, p, bnd, j);
        let div1j = div_succ(d, p, 1, j);
        rsub(d, rat, wj, div1j)
    };
    let zero_rat = rzero(d, rat);
    let cap = d.const_app(rat.max, &[raw, zero_rat]);
    let cap_nonneg = d.lemma(rat.le_max_right, &[raw, zero_rat]);
    let cap_le_raw_side = d.lemma(rat.le_max_left, &[raw, zero_rat]);

    let cap_le_bnd = {
        let raw_le_bnd = d.lemma(p.sample_lower_bound, &[bnd, j]);
        let rat_ty_e = rat_ty(d);
        let predicate = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let oft = d.const_app(p.of_rat, &[t]);
            let body = d.const_app(p.le, &[oft, bnd]);
            d.lam_fv(t_fv, rat_ty_e, body)
        };
        let on_le = {
            let h_fv = d.fresh_fvar();
            let hyp_ty = rle(d, rat, raw, zero_rat);
            d.lam_fv(h_fv, hyp_ty, hbnd0)
        };
        let on_ge = {
            let h_fv = d.fresh_fvar();
            let hyp_ty = rle(d, rat, zero_rat, raw);
            d.lam_fv(h_fv, hyp_ty, raw_le_bnd)
        };
        d.lemma(rat.max_cases, &[raw, zero_rat, predicate, on_le, on_ge])
    };

    // --- grid points, in [a,b] unconditionally. -----------------------------
    let gp_of = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
        let g = gp_rat(d, p, k, cap, i);
        let og = d.const_app(p.of_rat, &[g]);
        cadd(d, p, a, og)
    };
    let a_le_gp = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
        let g = gp_rat(d, p, k, cap, i);
        let gnn = gp_nonneg(d, p, k, cap, i, cap_nonneg);
        let og = d.const_app(p.of_rat, &[g]);
        let le0_og = d.lemma(p.of_rat_le, &[zero_rat, g, gnn]);
        shift_le_of_nonneg(d, p, a, og, le0_og)
    };
    let gp_le_b = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
        let g = gp_rat(d, p, k, cap, i);
        let gc = gp_le_cap(d, p, k, cap, i);
        let og = d.const_app(p.of_rat, &[g]);
        let ocap = d.const_app(p.of_rat, &[cap]);
        let og_le_ocap = d.lemma(p.of_rat_le, &[g, cap, gc]);
        let og_le_bnd = d.lemma(p.le_trans, &[og, ocap, bnd, og_le_ocap, cap_le_bnd]);
        let refl_a = d.lemma(p.le_refl, &[a]);
        let sum_le = d.lemma(p.add_le_add, &[a, a, og, bnd, refl_a, og_le_bnd]);
        let a_plus_og = cadd(d, p, a, og);
        let a_plus_bnd = cadd(d, p, a, bnd);
        let cancel = add_sub_cancel(d, p, a, b);
        let refl_apog = erefl(d, p, a_plus_og);
        d.lemma(
            p.le_congr,
            &[
                a_plus_og, a_plus_og, a_plus_bnd, b, refl_apog, cancel, sum_le,
            ],
        )
    };

    // --- consecutive grid points are `close_within … odeltauc`. -------------
    let gp_close = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
        let gi = gp_rat(d, p, k, cap, i);
        let succ_i = d.succ(i);
        let gsi = gp_rat(d, p, k, cap, succ_i);
        let ogi = d.const_app(p.of_rat, &[gi]);
        let ogsi = d.const_app(p.of_rat, &[gsi]);
        let delta = div_succ(d, p, 1, k);

        let diff_lower = gp_diff_lower(d, p, k, cap, i);
        let diff_upper = gp_diff_upper(d, p, k, cap, i);
        let h1_rat = d.lemma(rat.le_of_sub_le, &[gi, gsi, delta, diff_lower]);
        let h2_rat = d.lemma(rat.le_of_sub_le, &[gsi, gi, delta, diff_upper]);
        let h1_plain = of_rat_le_add(d, p, gi, gsi, delta, h1_rat);
        let h2_plain = of_rat_le_add(d, p, gsi, gi, delta, h2_rat);
        let odelta = d.const_app(p.of_rat, &[delta]);
        let close_plain_delta = close_of_bounds(d, p, ogi, ogsi, odelta, h1_plain, h2_plain);

        let dle = delta_le_delta_uc(d, p, k, m0);
        let widen = d.lemma(p.of_rat_le, &[delta, deltauc, dle]);
        let neg_ogsi = cneg(d, p, ogsi);
        let diff_gigsi = cadd(d, p, ogi, neg_ogsi);
        let abs_diff_gigsi = cabs(d, p, diff_gigsi);
        let close_plain = d.lemma(
            p.le_trans,
            &[abs_diff_gigsi, odelta, odeltauc, close_plain_delta, widen],
        );

        close_within_shift(d, p, a, ogi, ogsi, odeltauc, close_plain)
    };

    // --- the induction on `i`: `|F(GP i)| <= mag_bound(T i)`,
    // `T i := add (succ (bound (F a))) i`. -----------------------------------
    let f_a = d.apply(f, &[a]);
    let k_bound = ubound_of(d, p, f_a);
    let succ_k_bound = d.succ(k_bound);
    let t_of = |d: &mut IntDev<'_>, i: ExprId| -> ExprId { NatOps::add(d, succ_k_bound, i) };
    let stmt_at = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
        let gpi = gp_of(d, i);
        let fgpi = d.apply(f, &[gpi]);
        let absf = cabs(d, p, fgpi);
        let ti = t_of(d, i);
        let mb = mag_bound(d, p, ti);
        d.const_app(p.le, &[absf, mb])
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let gp0 = gp_rat(d, p, k, cap, zero_nat);
        let og0 = d.const_app(p.of_rat, &[gp0]);
        let gp0_full = cadd(d, p, a, og0);
        let delta = div_succ(d, p, 1, k);
        let odelta = d.const_app(p.of_rat, &[delta]);
        let raw0 = div_succ_at(d, p, zero_nat, k);

        let raw0_le_delta = d.lemma(rat.nat_div_succ_le_add_left, &[zero_nat, one_nat, k]);
        let gp0_le_raw0 = d.lemma(rat.min_le_left, &[raw0, cap]);
        let gp0_le_delta = d.lemma(
            rat.le_trans,
            &[gp0, raw0, delta, gp0_le_raw0, raw0_le_delta],
        );

        let h1 = {
            let agp0 = a_le_gp(d, zero_nat);
            let odelta_nonneg = {
                let le0 = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, k]);
                d.lemma(p.of_rat_le, &[zero_rat, delta, le0])
            };
            let gp0_shift = shift_le_of_nonneg(d, p, gp0_full, odelta, odelta_nonneg);
            let gp0_plus_odelta = cadd(d, p, gp0_full, odelta);
            d.lemma(p.le_trans, &[a, gp0_full, gp0_plus_odelta, agp0, gp0_shift])
        };
        let h2 = {
            let og0_le_odelta = d.lemma(p.of_rat_le, &[gp0, delta, gp0_le_delta]);
            let refl_a2 = d.lemma(p.le_refl, &[a]);
            d.lemma(p.add_le_add, &[a, a, og0, odelta, refl_a2, og0_le_odelta])
        };
        let close_a_gp0_delta = close_of_bounds(d, p, a, gp0_full, odelta, h1, h2);
        let dle = delta_le_delta_uc(d, p, k, m0);
        let widen = d.lemma(p.of_rat_le, &[delta, deltauc, dle]);
        let neg_gp0_full = cneg(d, p, gp0_full);
        let diff_a_gp0 = cadd(d, p, a, neg_gp0_full);
        let abs_diff_a_gp0 = cabs(d, p, diff_a_gp0);
        let close_a_gp0 = d.lemma(
            p.le_trans,
            &[abs_diff_a_gp0, odelta, odeltauc, close_a_gp0_delta, widen],
        );

        let hax = d.lemma(p.le_refl, &[a]);
        let hxb = hab;
        let hay = a_le_gp(d, zero_nat);
        let hyb = gp_le_b(d, zero_nat);
        let close_fa_fgp0 = d.apply(
            spec,
            &[zero_nat, a, gp0_full, hax, hxb, hay, hyb, close_a_gp0],
        );
        let fgp0 = d.apply(f, &[gp0_full]);
        let mb0 = mag_bound(d, p, zero_nat);
        let close_fgp0_fa = close_within_symm(d, p, f_a, fgp0, mb0, close_fa_fgp0);
        let hprev = d.lemma(p.abs_bound_of_self, &[f_a]);
        let mbk = mag_bound(d, p, k_bound);
        let step = triangle_step(d, p, f_a, fgp0, mbk, mb0, hprev, close_fgp0_fa);
        let fuse = mag_bound_fuse_succ(d, p, k_bound);
        let abs_fgp0 = cabs(d, p, fgp0);
        let refl_absfgp0 = erefl(d, p, abs_fgp0);
        let mb_succ_kb = mag_bound(d, p, succ_k_bound);
        let mbk_mb0 = cadd(d, p, mbk, mb0);
        d.lemma(
            p.le_congr,
            &[
                abs_fgp0,
                abs_fgp0,
                mbk_mb0,
                mb_succ_kb,
                refl_absfgp0,
                fuse,
                step,
            ],
        )
    };

    let step_fn = |d: &mut IntDev<'_>, i: ExprId, ih: ExprId| -> ExprId {
        let gpi = gp_of(d, i);
        let succ_i = d.succ(i);
        let gpsi = gp_of(d, succ_i);
        let fgpi = d.apply(f, &[gpi]);
        let fgpsi = d.apply(f, &[gpsi]);

        let close_gp = gp_close(d, i);
        let hax = a_le_gp(d, i);
        let hxb = gp_le_b(d, i);
        let hay = a_le_gp(d, succ_i);
        let hyb = gp_le_b(d, succ_i);
        let close_f = d.apply(spec, &[zero_nat, gpi, gpsi, hax, hxb, hay, hyb, close_gp]);
        let mb0 = mag_bound(d, p, zero_nat);
        let close_f_rev = close_within_symm(d, p, fgpi, fgpsi, mb0, close_f);

        let ti = t_of(d, i);
        let mbti = mag_bound(d, p, ti);
        let step = triangle_step(d, p, fgpi, fgpsi, mbti, mb0, ih, close_f_rev);
        let fuse = mag_bound_fuse_succ(d, p, ti);
        let abs_fgpsi = cabs(d, p, fgpsi);
        let refl_absfgpsi = erefl(d, p, abs_fgpsi);
        let succ_ti = d.succ(ti);
        let mb_succ_ti = mag_bound(d, p, succ_ti);
        let mbti_mb0 = cadd(d, p, mbti, mb0);
        d.lemma(
            p.le_congr,
            &[
                abs_fgpsi,
                abs_fgpsi,
                mbti_mb0,
                mb_succ_ti,
                refl_absfgpsi,
                fuse,
                step,
            ],
        )
    };

    // --- the outer bound `K`, independent of `z`. ---------------------------
    let bound_bnd = ubound_of(d, p, bnd);
    let succ_bound_bnd = d.succ(bound_bnd);
    let m_bound_base = NatOps::add(d, succ_bound_bnd, two_nat);
    let m_bound = NatOps::mul(d, m_bound_base, k1);
    let t_m_bound = t_of(d, m_bound);
    let k_final = d.succ(t_m_bound);

    // --- the `z`-quantified body. --------------------------------------------
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let haz_fv = d.fresh_fvar();
    let haz = d.kernel().fvar(haz_fv);
    let hzb_fv = d.fresh_fvar();
    let hzb = d.kernel().fvar(hzb_fv);

    let range_az = d.const_app(p.le, &[a, z]);
    let range_zb = d.const_app(p.le, &[z, b]);

    let body = {
        // `w := z - a`.
        let w = cadd(d, p, z, na);

        // h0w : le zero w, from haz (mirrors `hbnd0`, with `z` for `b`).
        let h0w = {
            let refl_na2 = d.lemma(p.le_refl, &[na]);
            let shifted = d.lemma(p.add_le_add, &[a, z, na, na, haz, refl_na2]);
            let a_na = cadd(d, p, a, na);
            let zero_c = czero(d, p);
            let hn = d.lemma(p.add_neg, &[a]);
            let refl_w = erefl(d, p, w);
            d.lemma(p.le_congr, &[a_na, zero_c, w, w, hn, refl_w, shifted])
        };

        // hle : le w bnd, from hzb.
        let hle = {
            let refl_na3 = d.lemma(p.le_refl, &[na]);
            d.lemma(p.add_le_add, &[z, b, na, na, hzb, refl_na3])
        };

        let m = d.const_app(p.bucket_index, &[w, k]);
        let m_bound_of_m = d.lemma(p.bucket_index_bound, &[w, bnd, k, hle]);
        // m_bound_of_m : Nat.le m (mul (add (succ (bound bnd)) 2) (succ k)) = Nat.le m m_bound

        let induction_proof = d.induct(&stmt_at, &base, &step_fn, m);
        // induction_proof : le (abs (F (GP m))) (mag_bound (T m))

        let t_m = t_of(d, m);
        let t_mono = d.lemma(
            nat_p.add_le_add_left,
            &[succ_k_bound, m, m_bound, m_bound_of_m],
        );
        // t_mono : Nat.le (add succ_k_bound m) (add succ_k_bound m_bound) = Nat.le (T m) t_m_bound
        let mag_mono = mag_bound_mono(d, p, t_m, t_m_bound, t_mono);
        let gpm = gp_of(d, m);
        let fgpm = d.apply(f, &[gpm]);
        let abs_fgpm = cabs(d, p, fgpm);
        let mag_t_m = mag_bound(d, p, t_m);
        let mag_t_m_bound = mag_bound(d, p, t_m_bound);
        let bound_on_gpm = d.lemma(
            p.le_trans,
            &[abs_fgpm, mag_t_m, mag_t_m_bound, induction_proof, mag_mono],
        );
        // bound_on_gpm : le (abs (F (GP m))) (mag_bound t_m_bound)

        // --- `z` close to `GP(m)`. --------------------------------------
        let close_w_gpm = d.lemma(
            p.bucket_close,
            &[bnd, m0, cap, cap_le_raw_side, w, h0w, hle],
        );
        // close_w_gpm : close_within w (ofRat (gp_rat k cap m)) odeltauc

        let gpm_rat = gp_rat(d, p, k, cap, m);
        let ogpm = d.const_app(p.of_rat, &[gpm_rat]);

        let close_aw_gpm = close_within_shift(d, p, a, w, ogpm, odeltauc, close_w_gpm);
        // close_aw_gpm : close_within (add a w) (add a ogpm) odeltauc
        //             == close_within (add a w) (GP m) odeltauc
        let heq_az = add_sub_cancel(d, p, a, z);
        // heq_az : Equiv (add a w) z
        let a_plus_w = cadd(d, p, a, w);
        let close_z_gpm =
            close_within_congr_left(d, p, a_plus_w, z, gpm, odeltauc, heq_az, close_aw_gpm);
        // close_z_gpm : close_within z (GP m) odeltauc

        let hay2 = a_le_gp(d, m);
        let hyb2 = gp_le_b(d, m);
        let close_fz_fgpm = d.apply(spec, &[zero_nat, z, gpm, haz, hzb, hay2, hyb2, close_z_gpm]);
        // close_fz_fgpm : close_within (F z) (F (GP m)) (mag_bound 0)

        let mb0_final = mag_bound(d, p, zero_nat);
        let fz = d.apply(f, &[z]);
        let final_step = triangle_step(
            d,
            p,
            fgpm,
            fz,
            mag_t_m_bound,
            mb0_final,
            bound_on_gpm,
            close_fz_fgpm,
        );
        let fuse_final = mag_bound_fuse_succ(d, p, t_m_bound);
        let abs_fz = cabs(d, p, fz);
        let refl_absfz = erefl(d, p, abs_fz);
        let mb_k_final = mag_bound(d, p, k_final);
        let mag_t_m_bound_plus_mb0 = cadd(d, p, mag_t_m_bound, mb0_final);
        d.lemma(
            p.le_congr,
            &[
                abs_fz,
                abs_fz,
                mag_t_m_bound_plus_mb0,
                mb_k_final,
                refl_absfz,
                fuse_final,
                final_step,
            ],
        )
    };

    let value = {
        let with_hzb = d.lam_fv(hzb_fv, range_zb, body);
        let with_haz = d.lam_fv(haz_fv, range_az, with_hzb);
        let with_z = d.lam_fv(z_fv, carrier, with_haz);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_z);
        let with_huc = d.lam_fv(huc_fv, huc_ty, with_hab);
        let with_b = d.lam_fv(b_fv, carrier, with_huc);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, func_ty, with_a)
    };
    let ty = {
        // `k_final` mentions `huc_fv` (via `modulus := uc_modulus f a b huc`),
        // so the hypothesis it depends on must be bound with `pi_fv`, not
        // `d.arrow` -- an `arrow` does not abstract the fvar out of `concl`,
        // which is exactly the `UnboundFVar` trap.
        let concl = bounded_on_applied(d, p, f, a, b, k_final);
        let with_hab = d.arrow(hab_ty, concl);
        let with_huc = d.pi_fv(huc_fv, huc_ty, with_hab);
        let with_b = d.pi_fv(b_fv, carrier, with_huc);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, func_ty, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bounded_of_uniformly_continuous,
        uparams: vec![],
        ty,
        value,
    })
}

/// `close_within x y q`'s TYPE (`le (abs (add x (neg y))) q`), for building
/// a `Rat.min_cases`/`Rat.max_cases` predicate whose branches each supply a
/// [`close_of_bounds`] value.
fn close_of_bounds_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let abs_diff = cabs(d, p, diff);
    d.const_app(p.le, &[abs_diff, q])
}
