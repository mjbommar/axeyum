//! **`CReal.natSqrt`**: the integer square root, by structural recursion, with
//! its defining two-sided bound — the missing computational primitive behind
//! `CReal.sqrt`.
//!
//! ## Why this file exists, and why it stops here
//!
//! `CReal.sqrt`'s only genuinely hard part is not real-analysis machinery —
//! `equiv_of_bounded`, `regular_between`, `fuse_at`
//! ([`super::product`]) and `ratSqLe`/`ratSqSandwich`
//! ([`super::mul_self_zero`]) already give the CReal-level estimate template
//! (see that module's docs: the sandwich lemma turns a rational bound on a
//! *square* directly into a `CReal.Within`, with no division and no case split
//! on which of two reals is bigger). What is missing is a **rational square
//! root approximation with a proven error bound**, and nothing in the trusted
//! library computes one: `RatPrelude` has no `sqrt`/`pow`-inverse, and the one
//! natural place to build it — `Nat`'s own integer square root — does not
//! exist in `nat_prelude` either.
//!
//! Building that primitive needs a genuine **decidable, data-level** search
//! (unlike every real-order fact in this module, which is `Prop`-valued and
//! cannot select data — see [`CReal.inv`](super::CRealPrelude::inv)'s own
//! docs on exactly this restriction). The tool that makes it possible without
//! any new axiom is [`NatOps::ble`](crate::nat_prelude::NatOps::ble) (`Bool`,
//! not `Prop`, so `Bool.rec` may select a `Nat` freely) together with
//! [`NatOps::bool_select_nat`](crate::nat_prelude::NatOps::bool_select_nat)
//! (already built, and already used by `Nat.div`/`Nat.mod`'s own executable
//! state — [`nat_prelude::division`](crate::nat_prelude) — which is the
//! template this file follows).
//!
//! **This slice stays at the `Nat` level on purpose.** Lifting `natSqrt` to a
//! rational approximant of a `CReal` sample needs a decidable comparison for
//! `Rat`/`Int` (built from `Nat.ble` by a constructor case split on `Int`,
//! itself unproblematic since `Int.rec` eliminates into any `Sort` — `Int` is
//! a `Type`, not a `Prop`) and then the sampling-index schedule that
//! compensates for `sqrt` **not** being Lipschitz at `0` (its modulus of
//! continuity is itself a square root: `|sqrt a − sqrt b| ≤ sqrt |a−b|`,
//! provable from `ratSqSandwich` applied to `sqrt a − sqrt b` without ever
//! dividing by `sqrt a + sqrt b`, which is what makes `0 ≤ x` — not
//! `PosBound x k` — the honest hypothesis for `CReal.sqrt`, unlike
//! `CReal.inv`: nothing here needs to *decide* how close to zero `x` is,
//! only to *sample deeper* as the target precision tightens). That remaining
//! climb is real-analysis-sized on its own (`CReal.mul`'s `product.rs` is
//! 2400+ lines; `mul_self_zero.rs`, reusing most of that, still took a
//! four-lane chain — its own commit message says so) and is exactly the
//! obstruction named in this slice's report, not solved by it.
//!
//! ## Update: the obstruction is real, but it is smaller than "the exact
//! Bishop bound" — [`declare_sqrt_approx_sq_bracket`] and `speedup.rs` narrow it
//!
//! Two things landed after the paragraph above was written, neither of which
//! this file cross-referenced until now (checked against
//! `prelude_theorem_inventory --include-constructed`, 2026-08-26: no
//! `CReal.sqrt`, no `KRegular`-instance for `sqrtApprox`, so the obstruction
//! is CONFIRMED still open, not stale — but it is not the obstruction this
//! paragraph originally described).
//!
//! **First, `speedup.rs`'s `KRegular`/`speedup`/`regular_of_kregular` mean
//! `CReal.sqrt` does NOT need the exact `1/(m+1)+1/(n+1)` bound at all.**
//! `regular_of_kregular : ∀ f c, KRegular f c → Regular (speedup f c)` closes
//! the "some constant factor" → "exactly Bishop's constant" gap generically,
//! with NO slack-widening step (`speedup.rs`'s own doc: "two rewrites, no
//! weakening step") — reindexing exactly divides the constant out. So the
//! real remaining obligation is `KRegular sqrtApprox c` for SOME `c`, which
//! is a strictly easier target than `Regular sqrtApprox` itself, and
//! `speedup.rs`'s own doc already names this as the sole gap it leaves open
//! ("proving `sqrtApprox` itself is `KRegular` for some concrete `c` ... is
//! the ~2000-line rational-inequality half `sqrt.rs`'s docs describe").
//!
//! **Second, [`declare_sqrt_approx_sq_bracket`] proves the SAME-INDEX piece
//! that `KRegular` has to be assembled from**: `(sqrtApprox x n)² ≤ q < ((s+1)/
//! (n+1))²`, `q := max(seq x (n+1)², 0)` — read back from
//! [`nat_floor_bracket`]'s `Nat`-level bracket via the identical
//! cross-multiplication route `uniform_continuity.rs` already uses for
//! `bucketIndex`'s own (unsquared) floor bound, confirming that file's "verbatim
//! in *recipe*" claim down to the lemma calls, not just the definition shape.
//!
//! **The remaining proof sketch, for the next lane** (not attempted here —
//! genuinely the ~2000-line half, even after the two shortcuts above): fix
//! `m, n`, write `d1 := m+1`, `d2 := n+1`, `u1 := sqrtApprox x m`,
//! `u2 := sqrtApprox x n`, `q1, q2` their respective clamped samples. WLOG
//! `u1 ≥ u2`. Chain: `u1² ≤ q1` (this file's own bracket) `≤ q2 + Δ` (`Δ :=
//! |q1−q2|`, from `Rat.sub_max_le` — `max` is 1-Lipschitz — composed with `x`'s
//! own `CReal.regular` at `(j1,j2)`) `< (u2 + natDivSucc 1 n)² + Δ` (this
//! file's own bracket, other direction). Setting `E := natDivSucc 1 m +
//! natDivSucc 1 n`, `Δ ≤ E²` holds because `Δ ≤ modulus(j1,j2) =
//! natDivSucc 1 (d1²) + natDivSucc 1 (d2²)`, each term strictly smaller than
//! the corresponding `1/d1²`/`1/d2²` term inside `E² = 1/d1² + 2/(d1·d2) +
//! 1/d2²` — so `(u2 + natDivSucc 1 n)² + Δ ≤ (u2 + natDivSucc 1 n + E)²`
//! (expand; the cross term `2·E·(u2+1/d2) ≥ 0` absorbs the rest), and
//! [`CRealPrelude::rat_sq_le`] (`u²≤s² → 0≤s → u≤s`, **no division by a sum of
//! roots anywhere**, exactly this file's own opening claim about
//! `ratSqSandwich`) gives `u1 ≤ u2 + natDivSucc 1 n + E = u2 + 2·natDivSucc 1 n
//! + natDivSucc 1 m ≤ u2 + 2·(natDivSucc 1 m + natDivSucc 1 n)`. The
//! symmetric case (`u2 ≥ u1`) is the same argument with `m`/`n` swapped, and
//! the two combine into `KRegular sqrtApprox 1` (`c = 1`, i.e. constant factor
//! `2`) — **independent of any magnitude bound on `x`**, unlike `CReal.mul`'s
//! canonical-bound machinery: `sqrt` is norm-*reducing*, and this route never
//! needs to know how big `x` is, only how close two of its samples are.

use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{
    den, den_pos, den_z, normalize, num, one_le_succ, rat_ty, rle, rlt, rzero,
};

use super::{CRealPrelude, DERIVED_HEIGHT, and_intro, creal_ty, sample};

/// `And left right`, as a `Prop`. Generic over what `left`/`right` are —
/// unlike [`super::equiv`]/[`super::within`], this file's statements are
/// plain `Nat` facts, so there is no `CReal`-specific packaging to reuse.
fn and_ty(d: &mut IntDev<'_>, p: CRealPrelude, left: ExprId, right: ExprId) -> ExprId {
    d.const_app(p.rat.int.logic.and, &[left, right])
}

/// `False.rec (fun _ => target) false_proof : target`.
///
/// A local copy of the identical private helper in `nat_prelude::fermat`,
/// `nat_prelude::totient`, `nat_prelude::order_more`, and
/// `nat_prelude::binomial` (each of those, in turn, a copy of the others) —
/// adapted here to `IntDev` since this module builds over `IntDev`, not
/// `NatDev`. Trivial enough (one `False.rec` application) that a fifth copy
/// costs nothing next to threading a `NatDev`-specific dependency through the
/// `creal` module boundary.
fn ex_falso(d: &mut IntDev<'_>, p: CRealPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let nat = p.rat.int.nat;
    let false_ty = d.kernel().const_(nat.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(nat.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `h : Lt zero n ⊢ Eq n (succ (pred n))` — i.e. `1 ≤ n → n = succ (pred n)`
/// (`Nat.lt zero n` is definitionally `Nat.le (succ zero) n = Nat.le 1 n`).
///
/// A local copy of `nat_prelude::finite::pos_implies_succ_pred` (itself
/// duplicated in `fermat.rs` and `totient.rs` — this is the fourth copy, and
/// per that helper's own doc comment, promoting it to a declared `Nat`
/// theorem reachable outside `nat_prelude` is the right long-term fix, not
/// attempted here). By induction on `n`: the base case is impossible via
/// `not_lt_zero`; the successor case is `refl`, since `pred (succ m)` reduces
/// to `m` definitionally. `n` may be any `Nat`-typed expression, not just a
/// bound variable — `Nat.rec` does not require its target to reduce.
fn one_le_implies_succ_pred(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let nat = p.rat.int.nat;
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let zero = d.zero();
        let hyp = d.lt(zero, x);
        let px = d.pred(x);
        let spx = d.succ(px);
        let concl = d.eq(x, spx);
        d.arrow(hyp, concl)
    };
    d.induct(
        &motive,
        &|d: &mut IntDev<'_>| {
            let zero = d.zero();
            let hyp_ty = d.lt(zero, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let pz = d.pred(zero);
            let spz = d.succ(pz);
            let target_ty = d.eq(zero, spz);
            let not_lt = d.lemma(nat.not_lt_zero, &[zero]);
            let false_proof = d.apply(not_lt, &[hyp]);
            let body = ex_falso(d, p, target_ty, false_proof);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        &|d: &mut IntDev<'_>, m: ExprId, _ih: ExprId| {
            let sm = d.succ(m);
            let zero = d.zero();
            let hyp_ty = d.lt(zero, sm);
            let hyp_fv = d.fresh_fvar();
            let _hyp = d.kernel().fvar(hyp_fv);
            let body = d.refl(sm);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        n,
    )
}

/// Step A's Nat-level floor bracket (`docs/mathematics-2026-08/diary-creal-sqrt.md`):
/// given a positive denominator `b` (`b_pos : Le one b`, e.g. `Rat.den_pos`)
/// and a dividend `scaled`, writing `k := Nat.div scaled b` and
/// `s := CReal.natSqrt k`, returns `s` together with
///
/// - `lower : Le (b*(s*s)) scaled`
/// - `upper : Lt scaled (b*((succ s)*(succ s)))`
///
/// **Derivation.** `one_le_implies_succ_pred` turns `b_pos` (`Lt zero b`,
/// definitionally `Le one b`) into `b = succ (pred b)`; rewriting
/// `Nat.div_mod_exec (pred b) scaled` along that equality (in both the
/// divisor position and inside the `div`/`mod` it names) gives `divMod b
/// scaled k (Nat.mod scaled b)` with `k` and `Nat.mod scaled b` matching the
/// `div`/`modulo` built directly from `b` — the rewrite target is chosen to
/// land exactly there so no further massaging is needed. `Nat.div_mod_bounds`
/// then gives `b*k ≤ scaled < b*(succ k)`. `natSqrtLe`/`natSqrtLt` give `s*s ≤
/// k < (succ s)*(succ s)` i.e. `succ k ≤ (succ s)*(succ s)`; `mul_le_mul_left`
/// scales both by `b` (`b*(s*s) ≤ b*k` and `b*(succ k) ≤ b*((succ
/// s)*(succ s))`), and `le_trans`/`lt_of_lt_of_le` compose each with the
/// `div_mod_bounds` half on the same side.
fn nat_floor_bracket(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    b: ExprId,
    b_pos: ExprId,
    scaled: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let nat = p.rat.int.nat;

    // b = succ (pred b).
    let succ_pred_fn = one_le_implies_succ_pred(d, p, b);
    let b_eq_succ_pred = d.apply(succ_pred_fn, &[b_pos]);
    let pred_b = d.pred(b);
    let sp = d.succ(pred_b);
    let sp_eq_b = d.symm(b, sp, b_eq_succ_pred);

    // The executable witness, stated at the successor-shaped divisor `sp`.
    let exec = d.lemma(nat.div_mod_exec, &[pred_b, scaled]);
    // exec : divMod sp scaled (Nat.div scaled sp) (Nat.mod scaled sp)

    // Rewrite `sp` to `b` throughout, via `sp_eq_b : Eq sp b`.
    let motive = d.eq_motive(sp, &|d, x| {
        let q = NatOps::div(d, scaled, x);
        let r = NatOps::modulo(d, scaled, x);
        d.div_mod(x, scaled, q, r)
    });
    let relation = d.transport(sp, motive, exec, b, sp_eq_b);
    // relation : divMod b scaled (Nat.div scaled b) (Nat.mod scaled b)

    let k = NatOps::div(d, scaled, b);
    let r = NatOps::modulo(d, scaled, b);
    let bounds = d.lemma(nat.div_mod_bounds, &[b, scaled, k, r]);
    let bounds = d.apply(bounds, &[relation]);
    // bounds : And (Le (b*k) scaled) (Lt scaled (b*(succ k)))
    let bk = d.mul(b, k);
    let lower_ty = d.le(bk, scaled);
    let succ_k = d.succ(k);
    let b_succ_k = d.mul(b, succ_k);
    let upper_ty = d.lt(scaled, b_succ_k);
    let bounds_lower = d.and_left(lower_ty, upper_ty, bounds);
    let bounds_upper = d.and_right(lower_ty, upper_ty, bounds);

    let s = d.const_app(p.nat_sqrt, &[k]);
    let ss = d.mul(s, s);
    // s*s <= k
    let sqrt_le = d.lemma(p.nat_sqrt_le, &[k]);
    // k < (succ s)*(succ s), i.e. succ k <= (succ s)*(succ s)
    let sqrt_lt = d.lemma(p.nat_sqrt_lt, &[k]);
    let succ_s = d.succ(s);
    let succ_s_sq = d.mul(succ_s, succ_s);

    // b*(s*s) <= b*k <= scaled.
    let b_ss = d.mul(b, ss);
    let scale_lower = d.lemma(nat.mul_le_mul_left, &[b, ss, k, sqrt_le]);
    let lower = d.lemma(nat.le_trans, &[b_ss, bk, scaled, scale_lower, bounds_lower]);

    // scaled < b*(succ k) <= b*((succ s)*(succ s)).
    let b_succ_s_sq = d.mul(b, succ_s_sq);
    let scale_upper = d.lemma(nat.mul_le_mul_left, &[b, succ_k, succ_s_sq, sqrt_lt]);
    let upper = d.lemma(
        nat.lt_of_lt_of_le,
        &[scaled, b_succ_k, b_succ_s_sq, bounds_upper, scale_upper],
    );

    (s, lower, upper)
}

/// `CReal.sqrtApproxSqBracket : ∀ x n,
///   And (Rat.le (Rat.mul S S) Q) (Rat.lt Q (Rat.mul S1 S1))`, where
/// (writing `d := succ n`, `j := d*d`, `q := Rat.max (CReal.seq x j)
/// Rat.zero`, `s :=` the same `Nat` [`declare_sqrt_approx`] computes)
/// `Q := q`, `S := Rat.normalize (Int.ofNat s) d _` — **definitionally**
/// `CReal.sqrtApprox x n` (that is its entire body) — and `S1 := Rat.normalize
/// (Int.ofNat (succ s)) d _`, the next candidate up.
///
/// The single-index approximation-quality bracket `sqrtApprox` was built to
/// satisfy but this file never stated in `Rat`: `(sqrtApprox x n)² ≤ q <
/// ((s+1)/d)²`. It is [`nat_floor_bracket`]'s own `Nat`-level bracket (called
/// here unmodified, at `scaled = a*j`), read back into `Rat` by the identical
/// cross-multiplication route
/// [`super::uniform_continuity::declare_bucket_index_floor`] already uses for
/// `bucketIndex` — this file's own module doc names that primitive as
/// "verbatim in *recipe*" to `sqrtApprox`, and this proof confirms it down to
/// the lemma calls: `Rat.int_mul_le_mul_right`/`int_le_of_mul_le_mul_right`
/// scale and cancel by the OTHER side's denominator, `Rat.normalize_cross`
/// supplies the one identity relating a `normalize`d representative's
/// numerator back to the value it was built from, and the result lands on
/// the cross-multiplied shape `Rat.le`/`Rat.lt` unfold to — exactly as there,
/// just with the linear numerator `m` replaced throughout by the squared
/// numerator `s*s` (`(s+1)*(s+1)` for the upper half).
///
/// **This is NOT [`CReal.sqrt`]'s missing `KRegular` property.** It compares
/// `sqrtApprox x n` against `x`'s OWN sample at the SAME index `n` — no
/// second index, no cross-index estimate, no use of
/// [`CRealPrelude::rat_sq_le`]/[`CRealPrelude::rat_sq_sandwich`]. It is the
/// per-index quality fact `KRegular sqrtApprox c` would have to be built
/// FROM: comparing `sqrtApprox x m` against `sqrtApprox x n` needs this
/// bracket applied once at `m` and once at `n`, `x`'s own regularity
/// relating the two different sample points `(m+1)²`/`(n+1)²`, and
/// `rat_sq_le`'s division-free squeeze (`u² ≤ s² → 0 ≤ s → u ≤ s`) applied to
/// `u := sqrtApprox x m` against `s := sqrtApprox x n + natDivSucc 1 m +
/// natDivSucc 1 n` (the two error terms folded additively, never as a
/// quotient) to turn the resulting bound on the SQUARES into one on the
/// approximants themselves — not attempted here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_sqrt_approx_sq_bracket(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = p.rat.int.nat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // --- shared setup, rebuilt identically to `declare_sqrt_approx`'s own recipe.
    let dd = d.succ(n);
    let j = NatOps::mul(d, dd, dd);
    let sample_q = sample(d, p, x, j);
    let zero_rat = rzero(d, rat);
    let q = d.const_app(rat.max, &[sample_q, zero_rat]);

    let q_nonneg = d.lemma(rat.le_max_right, &[sample_q, zero_rat]); // Rat.le 0 q
    let num_q = num(d, q);
    let num_q_nonneg = d.lemma(rat.int_nonneg_of_nonneg, &[q, q_nonneg]); // Int.le 0 (num q)
    let a = d.const_app(rat.int.nat_abs, &[num_q]);
    let num_q_eq = d.lemma(rat.int.of_nat_nat_abs_of_nonneg, &[num_q, num_q_nonneg]); // Eq (ofNat a) (num q)
    let b = den(d, q);
    let bz = den_z(d, q);
    let b_pos = den_pos(d, q);

    let scaled = NatOps::mul(d, a, j);
    let (s, lower, upper_strict) = nat_floor_bracket(d, p, b, b_pos, scaled);

    let pos_d = one_le_succ(d, n); // 1 <= dd
    let j_pos = d.lemma(nat.one_le_mul, &[dd, dd, pos_d, pos_d]); // 1 <= j

    let az = d.of_nat(a);
    let jz = d.of_nat(j);
    let sz = d.of_nat(s);
    let ssz = d.imul(sz, sz);

    // rep_s := normalize (s*s) j j_pos, defeq `Rat.mul (sqrtApprox x n) (sqrtApprox x n)`
    // ONLY after `normalize_mul_normalize` (a proved lemma, not unfolding) —
    // not needed here since the declared statement below is phrased directly
    // in terms of `rep_s`/`rep_s1`, which unfold `sqrtApprox`'s own recipe.
    let rep_s = normalize(d, ssz, j, j_pos);
    let nm = num(d, rep_s);
    let dm = den(d, rep_s);
    let dm_z = den_z(d, rep_s);
    let cross_s = d.lemma(rat.normalize_cross, &[ssz, j, j_pos]);
    // cross_s : Eq (nm*jz) (ssz*dm_z)

    // ============ LOWER: Rat.le rep_s q ============
    let lower_final = {
        let bz_ssz = d.imul(bz, ssz);
        let az_jz = d.imul(az, jz);
        let scaled_lower = d.lemma(rat.int_mul_le_mul_right, &[bz_ssz, az_jz, dm, lower]);
        // : Int.le (bz_ssz*dm_z) (az_jz*dm_z)
        let lhs0 = d.imul(bz_ssz, dm_z);
        let rhs0 = d.imul(az_jz, dm_z);

        let ssz_dmz = d.imul(ssz, dm_z);
        let nm_jz = d.imul(nm, jz);
        let cross_s_rev = d.isymm(nm_jz, ssz_dmz, cross_s); // Eq (ssz*dm_z)(nm*jz)

        let bz_sszdmz = d.imul(bz, ssz_dmz);
        let assoc_l1 = d.lemma(rat.int.mul_assoc, &[bz, ssz, dm_z]); // Eq lhs0 (bz*(ssz*dm_z))
        let bz_nmjz = d.imul(bz, nm_jz);
        let step_l2 = d.icongr(ssz_dmz, nm_jz, cross_s_rev, &|d, t| d.imul(bz, t));
        let bz_nm = d.imul(bz, nm);
        let bz_nm_jz = d.imul(bz_nm, jz);
        let assoc_l3 = d.lemma(rat.int.mul_assoc, &[bz, nm, jz]); // Eq ((bz*nm)*jz)(bz*(nm*jz))
        let assoc_l3_rev = d.isymm(bz_nm_jz, bz_nmjz, assoc_l3);
        let comm_l4 = d.lemma(rat.int.mul_comm, &[bz, nm]); // Eq (bz*nm)(nm*bz)
        let nm_bz = d.imul(nm, bz);
        let nm_bz_jz = d.imul(nm_bz, jz);
        let step_l4 = d.icongr(bz_nm, nm_bz, comm_l4, &|d, t| d.imul(t, jz));

        let (target_lhs, eq_lhs) = d.ichain(
            lhs0,
            &[
                (bz_sszdmz, assoc_l1),
                (bz_nmjz, step_l2),
                (bz_nm_jz, assoc_l3_rev),
                (nm_bz_jz, step_l4),
            ],
        );

        let jz_dmz = d.imul(jz, dm_z);
        let az_jzdmz = d.imul(az, jz_dmz);
        let assoc_r1 = d.lemma(rat.int.mul_assoc, &[az, jz, dm_z]); // Eq (rhs0)(az*(jz*dm_z))
        let dmz_jz = d.imul(dm_z, jz);
        let az_dmzjz = d.imul(az, dmz_jz);
        let comm_r2 = d.lemma(rat.int.mul_comm, &[jz, dm_z]); // Eq (jz*dm_z)(dm_z*jz)
        let step_r2 = d.icongr(jz_dmz, dmz_jz, comm_r2, &|d, t| d.imul(az, t));
        let az_dmz = d.imul(az, dm_z);
        let az_dmz_jz = d.imul(az_dmz, jz);
        let assoc_r3 = d.lemma(rat.int.mul_assoc, &[az, dm_z, jz]); // Eq ((az*dm_z)*jz)(az*(dm_z*jz))
        let assoc_r3_rev = d.isymm(az_dmz_jz, az_dmzjz, assoc_r3);

        let (target_rhs, eq_rhs) = d.ichain(
            rhs0,
            &[
                (az_jzdmz, assoc_r1),
                (az_dmzjz, step_r2),
                (az_dmz_jz, assoc_r3_rev),
            ],
        );

        let motive1 = d.ieq_motive(lhs0, &|d, x| d.ile(x, rhs0));
        let step1 = d.itransport(lhs0, motive1, scaled_lower, target_lhs, eq_lhs);
        let motive2 = d.ieq_motive(rhs0, &|d, x| d.ile(target_lhs, x));
        let step2 = d.itransport(rhs0, motive2, step1, target_rhs, eq_rhs);
        // step2 : Int.le ((nm*bz)*jz) ((az*dm_z)*jz)

        let lower_cross = d.lemma(
            rat.int_le_of_mul_le_mul_right,
            &[nm_bz, az_dmz, j, j_pos, step2],
        );
        // : Int.le (nm*bz) (az*dm_z)

        let eq_az_dmz = d.icongr(az, num_q, num_q_eq, &|d, t| d.imul(t, dm_z));
        let num_q_dmz = d.imul(num_q, dm_z);
        let motive3 = d.ieq_motive(az_dmz, &|d, x| d.ile(nm_bz, x));
        d.itransport(az_dmz, motive3, lower_cross, num_q_dmz, eq_az_dmz)
        // : Int.le (nm*bz) (num_q*dm_z)  ==defeq==  Rat.le rep_s q
    };

    // ============ UPPER: Rat.lt q rep_s1 ============
    let succ_s = d.succ(s);
    let s1z = d.of_nat(succ_s);
    let s1sq_z = d.imul(s1z, s1z);
    let rep_s1 = normalize(d, s1sq_z, j, j_pos);
    let nm1 = num(d, rep_s1);
    let dm1 = den(d, rep_s1);
    let dm1_z = den_z(d, rep_s1);
    let dm1_pos = den_pos(d, rep_s1);
    let cross_s1 = d.lemma(rat.normalize_cross, &[s1sq_z, j, j_pos]);
    // cross_s1 : Eq (nm1*jz) (s1sq_z*dm1_z)

    // `upper_strict : Nat.lt scaled (b*succ_s_sq)`, defeq `Int.lt az_jz bz_s1sqz`.
    let upper_final = {
        let az_jz = d.imul(az, jz);
        let bz_s1sqz = d.imul(bz, s1sq_z);
        let scaled_upper = d.lemma(
            rat.int_mul_lt_mul_right,
            &[az_jz, bz_s1sqz, dm1, dm1_pos, upper_strict],
        );
        // : Int.lt (az_jz*dm1_z) (bz_s1sqz*dm1_z)
        let lhs0 = d.imul(az_jz, dm1_z);
        let rhs0 = d.imul(bz_s1sqz, dm1_z);

        let jz_dm1z = d.imul(jz, dm1_z);
        let az_jzdm1z = d.imul(az, jz_dm1z);
        let assoc_l1 = d.lemma(rat.int.mul_assoc, &[az, jz, dm1_z]); // Eq lhs0 (az*(jz*dm1_z))
        let dm1z_jz = d.imul(dm1_z, jz);
        let az_dm1zjz = d.imul(az, dm1z_jz);
        let comm_l2 = d.lemma(rat.int.mul_comm, &[jz, dm1_z]); // Eq (jz*dm1_z)(dm1_z*jz)
        let step_l2 = d.icongr(jz_dm1z, dm1z_jz, comm_l2, &|d, t| d.imul(az, t));
        let az_dm1z = d.imul(az, dm1_z);
        let az_dm1z_jz = d.imul(az_dm1z, jz);
        let assoc_l3 = d.lemma(rat.int.mul_assoc, &[az, dm1_z, jz]); // Eq ((az*dm1_z)*jz)(az*(dm1_z*jz))
        let assoc_l3_rev = d.isymm(az_dm1z_jz, az_dm1zjz, assoc_l3);

        let (target_lhs, eq_lhs) = d.ichain(
            lhs0,
            &[
                (az_jzdm1z, assoc_l1),
                (az_dm1zjz, step_l2),
                (az_dm1z_jz, assoc_l3_rev),
            ],
        );

        let s1sqz_dm1z = d.imul(s1sq_z, dm1_z);
        let bz_s1sqzdm1z = d.imul(bz, s1sqz_dm1z);
        let assoc_r1 = d.lemma(rat.int.mul_assoc, &[bz, s1sq_z, dm1_z]); // Eq rhs0 (bz*(s1sqz*dm1_z))
        let nm1_jz = d.imul(nm1, jz);
        let cross_s1_rev = d.isymm(nm1_jz, s1sqz_dm1z, cross_s1); // Eq (s1sqz*dm1_z)(nm1*jz)
        let bz_nm1jz = d.imul(bz, nm1_jz);
        let step_r2 = d.icongr(s1sqz_dm1z, nm1_jz, cross_s1_rev, &|d, t| d.imul(bz, t));
        let bz_nm1 = d.imul(bz, nm1);
        let bz_nm1_jz = d.imul(bz_nm1, jz);
        let assoc_r3 = d.lemma(rat.int.mul_assoc, &[bz, nm1, jz]); // Eq ((bz*nm1)*jz)(bz*(nm1*jz))
        let assoc_r3_rev = d.isymm(bz_nm1_jz, bz_nm1jz, assoc_r3);
        let comm_r4 = d.lemma(rat.int.mul_comm, &[bz, nm1]); // Eq (bz*nm1)(nm1*bz)
        let nm1_bz = d.imul(nm1, bz);
        let nm1_bz_jz = d.imul(nm1_bz, jz);
        let step_r4 = d.icongr(bz_nm1, nm1_bz, comm_r4, &|d, t| d.imul(t, jz));

        let (target_rhs, eq_rhs) = d.ichain(
            rhs0,
            &[
                (bz_s1sqzdm1z, assoc_r1),
                (bz_nm1jz, step_r2),
                (bz_nm1_jz, assoc_r3_rev),
                (nm1_bz_jz, step_r4),
            ],
        );

        let motive1 = d.ieq_motive(lhs0, &|d, x| d.ilt(x, rhs0));
        let step1 = d.itransport(lhs0, motive1, scaled_upper, target_lhs, eq_lhs);
        let motive2 = d.ieq_motive(rhs0, &|d, x| d.ilt(target_lhs, x));
        let step2 = d.itransport(rhs0, motive2, step1, target_rhs, eq_rhs);
        // step2 : Int.lt ((az*dm1_z)*jz) ((nm1*bz)*jz)

        let upper_cross = d.lemma(
            rat.int_lt_of_mul_lt_mul_right,
            &[az_dm1z, nm1_bz, j, j_pos, step2],
        );
        // : Int.lt (az*dm1_z) (nm1*bz)

        let eq_az_dm1z = d.icongr(az, num_q, num_q_eq, &|d, t| d.imul(t, dm1_z));
        let num_q_dm1z = d.imul(num_q, dm1_z);
        let motive3 = d.ieq_motive(az_dm1z, &|d, x| d.ilt(x, nm1_bz));
        d.itransport(az_dm1z, motive3, upper_cross, num_q_dm1z, eq_az_dm1z)
        // : Int.lt (num_q*dm1_z) (nm1*bz)  ==defeq==  Rat.lt q rep_s1
    };

    let stmt_lower = rle(d, rat, rep_s, q);
    let stmt_upper = rlt(d, rat, q, rep_s1);
    let stmt = and_ty(d, p, stmt_lower, stmt_upper);
    let proof = and_intro(d, p, stmt_lower, stmt_upper, lower_final, upper_final);

    let value = {
        let with_n = d.lam_fv(n_fv, nat_ty, proof);
        d.lam_fv(x_fv, carrier, with_n)
    };
    let ty = {
        let over_n = d.pi_fv(n_fv, nat_ty, stmt);
        d.pi_fv(x_fv, carrier, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sqrt_approx_sq_bracket,
        uparams: vec![],
        ty,
        value,
    })
}

/// From `h : Eq Bool b Bool.false`, derive `Not (Eq Bool b Bool.true)`.
///
/// `b`'s two possible values are mutually exclusive
/// ([`NatOps::false_true_elim`](crate::nat_prelude::NatOps::false_true_elim)
/// is the existing `Bool.false ≠ Bool.true` discriminator); this is the
/// one-line bridge from "`b` computed to `false`" to "`b` did not compute to
/// `true`", needed to reach [`RatPrelude`](crate::RatPrelude)'s Nat-level
/// `not_le_of_not_ble_eq_true` from the *other* branch of a
/// [`NatOps::bool_select_nat`] discriminant.
fn not_bool_eq_true_of_false(d: &mut IntDev<'_>, b: ExprId, h_false: ExprId) -> ExprId {
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let sym = d.bool_symm(b, false_, h_false);
    let h2_ty = d.bool_eq(b, true_);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let contra = d.bool_trans(false_, b, true_, sym, h2);
    let false_name = d.prelude().logic.false_;
    let false_ty = d.kernel().const_(false_name, vec![]);
    let body = d.false_true_elim(false_ty, contra);
    d.lam_fv(h2_fv, h2_ty, body)
}

/// `Nat.le (Nat.succ (Nat.mul a a)) (Nat.mul (Nat.succ a) (Nat.succ a))` —
/// `(a+1)² ≥ a²+1`, the one algebraic fact the successor case of
/// [`declare_nat_sqrt_spec`] needs to grow the upper bound.
///
/// `(a+1)·(a+1) = ((a·a)+a)+(a+1)` (`succ_mul` then `mul_succ`, folded by one
/// `congr`); `succ(a·a) = (a·a)+1 ≤ (a·a)+(a+1)` (`1 ≤ a+1` is
/// `le_succ_succ` at `zero_le a`, scaled by `add_le_add_left`); and
/// `(a·a)+(a+1) ≤ ((a·a)+a)+(a+1)` is `le_add_right` scaled by
/// `add_le_add_right`. `le_trans` composes the two, and the whole thing is
/// rewritten back along the opening identity.
fn sq_step_bound(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let nat = p.rat.int.nat;
    let pa = d.mul(a, a);
    let succ_a = d.succ(a);

    // (a+1)*(a+1) = ((a*a)+a)+(a+1).
    let a_succ_a = d.mul(a, succ_a);
    let pa_plus_a = d.add(pa, a);
    let step_succ_mul = d.const_app(nat.succ_mul, &[a, succ_a]);
    let step_mul_succ = d.const_app(nat.mul_succ, &[a, a]);
    let lhs0 = d.mul(succ_a, succ_a);
    let mid0 = d.add(a_succ_a, succ_a);
    let rhs0 = d.add(pa_plus_a, succ_a);
    let congr1 = d.congr(a_succ_a, pa_plus_a, step_mul_succ, &|d, t| d.add(t, succ_a));
    let (_, whole_eq) = d.chain(lhs0, &[(mid0, step_succ_mul), (rhs0, congr1)]);

    // succ(a*a) <= (a*a) + (a+1), via (a*a)+1 = succ(a*a) and 1 <= a+1.
    let zero = d.zero();
    let one = d.succ(zero);
    let zero_le_a = d.const_app(nat.zero_le, &[a]);
    let one_le_succ_a = d.const_app(nat.le_succ_succ, &[zero, a, zero_le_a]);
    let pa_one = d.add(pa, one);
    let pa_succ_a = d.add(pa, succ_a);
    let add_le_1 = d.const_app(nat.add_le_add_left, &[pa, one, succ_a, one_le_succ_a]);
    let add_succ_pa = d.const_app(nat.add_succ, &[pa, zero]);
    let pa_zero = d.add(pa, zero);
    let add_zero_pa = d.const_app(nat.add_zero, &[pa]);
    let congr2 = d.congr(pa_zero, pa, add_zero_pa, &|d, t| d.succ(t));
    let succ_pa_zero = d.succ(pa_zero);
    let succ_pa = d.succ(pa);
    let (_, pa_one_eq_succ_pa) = d.chain(pa_one, &[(succ_pa_zero, add_succ_pa), (succ_pa, congr2)]);
    let add_le_1_at_succ_pa = {
        let motive = d.eq_motive(pa_one, &|d, t| d.le(t, pa_succ_a));
        d.transport(pa_one, motive, add_le_1, succ_pa, pa_one_eq_succ_pa)
    };
    // add_le_1_at_succ_pa : Le (succ pa) pa_succ_a

    // (a*a)+(a+1) <= ((a*a)+a)+(a+1), via (a*a) <= (a*a)+a.
    let le_add_right_pa_a = d.const_app(nat.le_add_right, &[pa, a]);
    let add_le_2 = d.const_app(
        nat.add_le_add_right,
        &[succ_a, pa, pa_plus_a, le_add_right_pa_a],
    );
    // add_le_2 : Le pa_succ_a rhs0

    let combined = d.const_app(
        nat.le_trans,
        &[succ_pa, pa_succ_a, rhs0, add_le_1_at_succ_pa, add_le_2],
    );
    // combined : Le (succ pa) rhs0

    let whole_eq_rev = d.symm(lhs0, rhs0, whole_eq);
    let motive2 = d.eq_motive(rhs0, &|d, t| d.le(succ_pa, t));
    d.transport(rhs0, motive2, combined, lhs0, whole_eq_rev)
}

/// `CReal.natSqrt : Nat -> Nat`, by structural recursion:
///
/// ```text
/// natSqrt 0        = 0
/// natSqrt (succ j) = let c := succ (natSqrt j)
///                     if Nat.ble (c*c) (succ j) then c else natSqrt j
/// ```
///
/// The single running candidate (rather than `Nat.choose`'s two-argument row,
/// or `Nat.div`/`Nat.mod`'s shared quotient/remainder state) is enough here:
/// unlike division, there is nothing to reset, only ever to grow by at most
/// one per step.
fn declare_nat_sqrt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = d.zero();
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let candidate = d.succ(ih);
        let succ_j = d.succ(j);
        let sq = d.mul(candidate, candidate);
        let cond = d.ble(sq, succ_j);
        let selected = d.bool_select_nat(cond, candidate, ih);
        let with_ih = d.lam_fv(ih_fv, nat, selected);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec = d.kernel().const_(p.rat.int.nat.rec, vec![one]);
    let body = d.apply(rec, &[motive, base, step, n]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    // Strictly greater delta height than `Nat.mul`/`Nat.ble` (both height 1).
    d.kernel().add_declaration(Declaration::Definition {
        name: p.nat_sqrt,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })
}

/// `CReal.natSqrtSpec : ∀ n,
///   And (Nat.le (natSqrt n * natSqrt n) n)
///       (Nat.lt n (succ (natSqrt n) * succ (natSqrt n)))`.
///
/// By induction on `n`, proving both halves together (the successor case
/// needs the upper-bound IH to grow the lower bound and vice versa). The
/// step case's discriminant is exactly `natSqrt`'s own `Nat.ble` test; the
/// standard `Bool.rec`-applied-to-the-discriminant-itself trick (as in
/// `nat_prelude::division`'s executable spec proof) recovers each branch as
/// a hypothesis without a separate "cases on this Bool" lemma.
fn declare_nat_sqrt_spec(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = p.rat.int.nat;

    let spec = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        and_ty(d, p, left, right)
    };

    d.theorem(p.nat_sqrt_spec, 1, &|d, v| {
        let n = v[0];
        let stmt = spec(d, n);
        let proof = d.induct(
            &spec,
            &|d| {
                let zero = d.zero();
                let sqrt0 = d.const_app(p.nat_sqrt, &[zero]);
                let ss0 = d.mul(sqrt0, sqrt0);
                let left_ty = d.le(ss0, zero);
                let left_proof = d.const_app(nat.le_refl, &[zero]);
                let succ_sqrt0 = d.succ(sqrt0);
                let rhs = d.mul(succ_sqrt0, succ_sqrt0);
                let right_ty = d.lt(zero, rhs);
                let right_proof = d.zero_lt_succ(sqrt0);
                and_intro(d, p, left_ty, right_ty, left_proof, right_proof)
            },
            &|d, j, ih| {
                let s = d.const_app(p.nat_sqrt, &[j]);
                let ss = d.mul(s, s);
                let left_ih_ty = d.le(ss, j);
                let succ_s = d.succ(s);
                let s1s1 = d.mul(succ_s, succ_s);
                let right_ih_ty = d.lt(j, s1s1);
                let ih_left = d.and_left(left_ih_ty, right_ih_ty, ih);
                let ih_right = d.and_right(left_ih_ty, right_ih_ty, ih);

                let succ_j = d.succ(j);
                let condition = d.ble(s1s1, succ_j);
                let bool_ty = d.bool_ty();

                let target_for = |d: &mut IntDev<'_>, selector: ExprId| -> ExprId {
                    let next = d.bool_select_nat(selector, succ_s, s);
                    let next_sq = d.mul(next, next);
                    let l = d.le(next_sq, succ_j);
                    let succ_next = d.succ(next);
                    let r_rhs = d.mul(succ_next, succ_next);
                    let r = d.lt(succ_j, r_rhs);
                    and_ty(d, p, l, r)
                };
                let branch_for = |d: &mut IntDev<'_>, selector: ExprId| -> ExprId {
                    let eqty = d.bool_eq(condition, selector);
                    let tgt = target_for(d, selector);
                    d.arrow(eqty, tgt)
                };

                let false_ = d.bool_false();
                let false_minor = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_ty = d.bool_eq(condition, false_);
                    let left_proof = d.const_app(nat.le_step, &[ss, j, ih_left]);
                    let not_true = not_bool_eq_true_of_false(d, condition, h);
                    let not_le =
                        d.const_app(nat.not_le_of_not_ble_eq_true, &[s1s1, succ_j, not_true]);
                    let right_proof = d.const_app(nat.lt_of_not_le, &[s1s1, succ_j, not_le]);
                    let left_ty = d.le(ss, succ_j);
                    let right_ty = d.lt(succ_j, s1s1);
                    let body = and_intro(d, p, left_ty, right_ty, left_proof, right_proof);
                    d.lam_fv(h_fv, h_ty, body)
                };

                let true_ = d.bool_true();
                let true_minor = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_ty = d.bool_eq(condition, true_);
                    let left_proof = d.const_app(nat.le_of_ble_eq_true, &[s1s1, succ_j, h]);

                    let succ_succ_j = d.succ(succ_j);
                    let succ_s1s1 = d.succ(s1s1);
                    let step1 = d.const_app(nat.le_succ_succ, &[succ_j, s1s1, ih_right]);
                    let bound2 = sq_step_bound(d, p, succ_s);
                    let succ_s1 = d.succ(succ_s);
                    let target_rhs = d.mul(succ_s1, succ_s1);
                    let right_proof = d.const_app(
                        nat.le_trans,
                        &[succ_succ_j, succ_s1s1, target_rhs, step1, bound2],
                    );

                    let left_ty = d.le(s1s1, succ_j);
                    let right_ty = d.lt(succ_j, target_rhs);
                    let body = and_intro(d, p, left_ty, right_ty, left_proof, right_proof);
                    d.lam_fv(h_fv, h_ty, body)
                };

                let motive = {
                    let selector_fv = d.fresh_fvar();
                    let selector = d.kernel().fvar(selector_fv);
                    let body = branch_for(d, selector);
                    d.lam_fv(selector_fv, bool_ty, body)
                };
                let level_zero = d.kernel().level_zero();
                let bool_rec = d
                    .kernel()
                    .const_(p.rat.int.logic.bool_rec, vec![level_zero]);
                let selected = d.apply(bool_rec, &[motive, false_minor, true_minor, condition]);
                let refl_cond = d.bool_refl(condition);
                d.apply(selected, &[refl_cond])
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `CReal.natSqrtLe : ∀ n, Nat.le (natSqrt n * natSqrt n) n` — the lower
/// projection of [`declare_nat_sqrt_spec`].
fn declare_nat_sqrt_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    d.theorem(p.nat_sqrt_le, 1, &|d, v| {
        let n = v[0];
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        let spec_const = d.kernel().const_(p.nat_sqrt_spec, vec![]);
        let full = d.apply(spec_const, &[n]);
        let proof = d.and_left(left, right, full);
        (left, proof)
    })?;
    Ok(())
}

/// `CReal.natSqrtLt : ∀ n, Nat.lt n (succ (natSqrt n) * succ (natSqrt n))` —
/// the upper projection of [`declare_nat_sqrt_spec`].
fn declare_nat_sqrt_lt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    d.theorem(p.nat_sqrt_lt, 1, &|d, v| {
        let n = v[0];
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        let spec_const = d.kernel().const_(p.nat_sqrt_spec, vec![]);
        let full = d.apply(spec_const, &[n]);
        let proof = d.and_right(left, right, full);
        (right, proof)
    })?;
    Ok(())
}

/// `CReal.sqrtApprox : CReal → Nat → Rat` — the rational approximant
/// `CReal.sqrt` will be built from.
///
/// ```text
/// sqrtApprox x n :=
///   let d := n + 1                                -- Nat
///   let j := d * d                                 -- Nat, the sample index
///   let q := Rat.max (CReal.seq x j) Rat.zero        -- Rat, clamped >= 0
///   let a := Int.natAbs (Rat.num q)                   -- Nat
///   let b := Rat.den q                                 -- Nat, >= 1
///   let k := Nat.div (a * j) b                          -- Nat
///   let s := CReal.natSqrt k                             -- Nat
///   Rat.normalize (Int.ofNat s) d (one_le_succ n)          -- Rat, "= s/d"
/// ```
///
/// **Why this shape.** Sampling `x` at `j = (n+1)²` rather than `n` puts `q`
/// within `Rat.natDivSucc 1 j = 1/((n+1)²+1)` of `x` — finer than the
/// `1/(n+1)²` the non-Lipschitz-at-0 modulus of `√` needs (module docs above)
/// — with **no `Nat` subtraction**. Clamping with `Rat.max q Rat.zero` needs
/// no case split on `x`'s sign (`Rat.max` dispatches on the representation,
/// [`super::lattice`]) and the hypothesis `0 ≤ x` is not consumed here at
/// all — matching the recorded signature decision that `sqrt`'s hypothesis
/// is needed only *inside proofs*, never as data driving the construction.
/// Reusing `j = d*d` as **both** the sample index and the fixed-point scale
/// (rather than an independent precision parameter) is what keeps this a
/// bare `Nat.rec`-free definition with no side proof obligation: `a*j` and
/// `b` are both already-computed naturals, and `Nat.div` is total.
///
/// **What this declaration does NOT establish.** `s/d` is within `O(1/d)` of
/// `√x` — from `natSqrtSpec` (`s² ≤ k < (s+1)²`, so `s/d ≤ √(k/j) < (s+1)/d`
/// since `j = d²`), plus the `Nat.div` floor error on `k` vs `a*j/b` (also
/// `O(1/d)` after dividing by `d`, via the same "`√` moves a gap of `ε` to a
/// gap of `√ε`" fact `ratSqLe`/`ratSqSandwich` already prove at the rational
/// level), plus `q`'s `O(1/d²)` distance from `x` contributing another
/// `O(1/d)` through that same non-Lipschitz modulus — but turning that into
/// the *exact* Bishop bound `CReal.Regular` demands (`|s(m)/d(m) - s(n)/d(n)|
/// ≤ 1/(m+1) + 1/(n+1)`, no free constant) is a genuine rational-inequality
/// argument that has not been built. See the module docs' closing paragraph
/// and this slice's final report for exactly what is missing.
pub(super) fn declare_sqrt_approx(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat_carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let dd = d.succ(n);
    let j = NatOps::mul(d, dd, dd);
    let sample_q = sample(d, p, x, j);
    let zero_rat = rzero(d, p.rat);
    let q_pos = d.const_app(p.rat.max, &[sample_q, zero_rat]);
    let numerator = num(d, q_pos);
    let a = d.const_app(p.rat.int.nat_abs, &[numerator]);
    let b = den(d, q_pos);
    let scaled = NatOps::mul(d, a, j);
    let k = NatOps::div(d, scaled, b);
    let s = d.const_app(p.nat_sqrt, &[k]);
    let s_int = d.of_nat(s);
    let pos = one_le_succ(d, n);
    let body = normalize(d, s_int, dd, pos);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(x_fv, carrier, with_n)
    };
    let ty = {
        let inner = d.arrow(nat, rat_carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sqrt_approx,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 43),
    })
}

/// Admit `CReal.natSqrt`, `CReal.natSqrtSpec`, `CReal.natSqrtLe`,
/// `CReal.natSqrtLt`, `CReal.sqrtApprox`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_sqrt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_nat_sqrt(d, p)?;
    declare_nat_sqrt_spec(d, p)?;
    declare_nat_sqrt_le(d, p)?;
    declare_nat_sqrt_lt(d, p)?;
    declare_sqrt_approx(d, p)?;
    declare_sqrt_approx_sq_bracket(d, p)
}

#[cfg(test)]
mod bridging_smoke_tests {
    use super::*;
    use crate::int_prelude::ops::IntDev;

    /// Smoke-checks [`one_le_implies_succ_pred`] (the local copy of bridging
    /// piece 1 from the sqrt route's "what is left" list) by wrapping it in
    /// a declared theorem and letting the kernel accept or reject it —
    /// building the Rust closures is not evidence the *term* is well-typed,
    /// only `Kernel::add_declaration`'s trusted checker is.
    #[test]
    fn one_le_implies_succ_pred_type_checks() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let nat = d.nat_ty();
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let zero = d.zero();
        let hyp = d.lt(zero, n);
        let pn = d.pred(n);
        let spn = d.succ(pn);
        let concl = d.eq(n, spn);
        let inner_ty = d.arrow(hyp, concl);

        let body = one_le_implies_succ_pred(&mut d, p, n);

        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.pi_fv(n_fv, nat, inner_ty);

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "sqrtSmokeOneLeImpliesSuccPred");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "one_le_implies_succ_pred must kernel-check: {:?}",
            result.err()
        );
    }

    /// Smoke-checks [`nat_floor_bracket`] (Step A's Nat-level core) at
    /// symbolic `b`/`scaled`, with the hypothesis stated the way
    /// [`crate::rat_prelude::ops::den_pos`] actually delivers it (`Le one
    /// b`, not `Lt zero b`) — the real call site (`sqrtApprox`'s `den q`)
    /// supplies exactly that shape, and `one_le_implies_succ_pred` expects
    /// `Lt zero b`; this checks the kernel accepts the unfolding without an
    /// explicit conversion step.
    #[test]
    fn nat_floor_bracket_type_checks() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let nat = d.nat_ty();
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let scaled_fv = d.fresh_fvar();
        let scaled = d.kernel().fvar(scaled_fv);

        let zero = d.zero();
        let one = d.succ(zero);
        let bpos_ty = d.le(one, b);
        let bpos_fv = d.fresh_fvar();
        let bpos = d.kernel().fvar(bpos_fv);

        let (s, lower, upper) = nat_floor_bracket(&mut d, p, b, bpos, scaled);

        let ss = d.mul(s, s);
        let b_ss = d.mul(b, ss);
        let lower_ty = d.le(b_ss, scaled);

        let succ_s = d.succ(s);
        let succ_s_sq = d.mul(succ_s, succ_s);
        let b_succ_s_sq = d.mul(b, succ_s_sq);
        let upper_ty = d.lt(scaled, b_succ_s_sq);

        let body = and_intro(&mut d, p, lower_ty, upper_ty, lower, upper);
        let concl_ty = and_ty(&mut d, p, lower_ty, upper_ty);

        let with_bpos_value = d.lam_fv(bpos_fv, bpos_ty, body);
        let with_bpos_ty = d.arrow(bpos_ty, concl_ty);
        let with_scaled_value = d.lam_fv(scaled_fv, nat, with_bpos_value);
        let with_scaled_ty = d.pi_fv(scaled_fv, nat, with_bpos_ty);
        let value = d.lam_fv(b_fv, nat, with_scaled_value);
        let ty = d.pi_fv(b_fv, nat, with_scaled_ty);

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "sqrtSmokeNatFloorBracket");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "nat_floor_bracket must kernel-check: {:?}",
            result.err()
        );
    }
}
