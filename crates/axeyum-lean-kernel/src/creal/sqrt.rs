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
//!
//! ## Update: the sketch above is now landed, as [`declare_sqrt_approx_kregular`]
//!
//! `CReal.sqrtApproxKRegular : ∀ x, KRegular (sqrtApprox x) 1` is a kernel
//! declaration now (checked, axiom-free, confirmed by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`), built
//! via [`one_sided_bound`] (the cross-index squeeze sketched above, applied
//! once per direction rather than by a WLOG case split — both directions are
//! symmetric applications of the same `rat_sq_le` squeeze, so no
//! `Rat.le_or_lt` case analysis was needed after all) and
//! [`raw_bound_le_double`]/[`double_div_succ_eq`] (widening the raw bound to
//! the exact `c = 1` modulus). [`declare_sqrt_ctor`] then gives `CReal.sqrt`
//! directly: `sqrt x := CReal.mk (speedup (sqrtApprox x) 1)
//! (regular_of_kregular (sqrtApprox x) 1 (sqrtApproxKRegular x))` — the same
//! `CReal.mk`-via-`speedup` recipe `convergence.rs`'s `converges_of_cauchy`
//! already uses, so no `Exists.rec` elimination is needed. `CReal.sqrt` is
//! **total**: `sqrtApprox` clamps every sample to `Rat.max _ 0`, so the
//! construction never inspects `x`'s sign, and `0 ≤ x` is not part of its
//! signature.
//!
//! One shape mismatch cost real debugging time and is worth naming:
//! [`CRealPrelude::sqrt_approx_sq_bracket`]'s own conclusion states the
//! square as a single COLLAPSED `Rat.normalize` over the sample index
//! (`Rat.normalize (s*s) j _`), not as `Rat.mul (sqrtApprox x n) (sqrtApprox
//! x n)` — those two are only PROPOSITIONALLY equal, via
//! `Rat.normalize_mul_normalize`, not definitionally, so [`one_sided_bound`]
//! projects the bracket at its actual collapsed shape and bridges to the
//! squared-`sqrtApprox` form explicitly (see its own doc comment). A
//! previous version of this file's own doc restated the bracket using
//! `Rat.mul` directly, which is the SAME error this module's own opening
//! section warns against making with `sqrtApprox` vs. its bracket.
//!
//! `sq_sqrt`/`sqrt_sq` (relating `sqrt x` back to `x` by squaring) are
//! **not attempted**. Squaring `sqrt x` goes through `CReal.mul`'s own
//! sampling (`mulShift`/`mul_index`), which needs a canonical bound on `sqrt
//! x` itself — exactly the magnitude-bound machinery this `KRegular` proof
//! deliberately avoided — plus composing two layers of sampling index
//! (`mul`'s own, `speedup`'s) before the `sqrtApproxSqBracket`-based
//! convergence squeeze (via `CRealPrelude::equiv_of_bounded`) can even be
//! stated. That is real, comparably-sized additional work.
//!
//! A concrete regression test lives in `creal_tests.rs`:
//! `CReal.seq (CReal.sqrt (CReal.ofNat 4)) 0` computes, by kernel reduction
//! alone, to `Rat.natDivSucc 2 0` (`= 2`), with a negative control (`3`) the
//! kernel rejects.

use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    den, den_pos, den_z, normalize, num, one_le_succ, radd, rat_eq_rewrite, rat_ty, rchain, rcongr,
    rle, rlt, rmul, rneg, rone, rsymm, rzero,
};

use super::product::{index_le, mul_index};
use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, creal_ty, div_succ, equiv, halves, modulus, sample,
    weaken, within,
};

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

// =============================================================================
// `KRegular sqrtApprox 1`, and `CReal.sqrt` from it.
//
// This section closes the obligation this module's own doc names as the
// remaining `~2000-line rational-inequality half`: `sqrtApprox` is `KRegular`
// with constant `c = 1`, so `speedup.rs`'s `regular_of_kregular` gives
// `CReal.sqrt` directly via `CReal.mk`, with no exact-Bishop-bound argument
// ever attempted. See each function's own doc for its piece of the argument
// sketched in this module's top-level doc comment.
// =============================================================================

/// `Eq Rat ((a+b)*c) (a*c+b*c)` — right-distributivity at `Rat`, derived from
/// `Rat.left_distrib` (only the left form is declared) plus `mul_comm`: one
/// commute to put the sum on the right, `left_distrib` to open it, two more
/// commutes to restore each factor's original order.
fn rat_right_distrib(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let rat = p.rat;
    let a_plus_b = radd(d, a, b);
    let start = rmul(d, a_plus_b, c);
    let step1 = d.lemma(rat.mul_comm, &[a_plus_b, c]);
    let c_ab = rmul(d, c, a_plus_b);
    let step2 = d.lemma(rat.left_distrib, &[c, a, b]);
    let ca = rmul(d, c, a);
    let cb = rmul(d, c, b);
    let ca_cb = radd(d, ca, cb);
    let ac = rmul(d, a, c);
    let comm_ca = d.lemma(rat.mul_comm, &[c, a]);
    let step3 = rcongr(d, ca, ac, comm_ca, &|d, t| {
        let cb2 = rmul(d, c, b);
        radd(d, t, cb2)
    });
    let ac_cb = radd(d, ac, cb);
    let bc = rmul(d, b, c);
    let comm_cb = d.lemma(rat.mul_comm, &[c, b]);
    let step4 = rcongr(d, cb, bc, comm_cb, &|d, t| radd(d, ac, t));
    let ac_bc = radd(d, ac, bc);
    let (_, whole) = rchain(
        d,
        start,
        &[
            (c_ab, step1),
            (ca_cb, step2),
            (ac_cb, step3),
            (ac_bc, step4),
        ],
    );
    whole
}

/// `Eq Int ((a+b)*c) (a*c+b*c)` — the `Int`-level twin of
/// [`rat_right_distrib`], needed inside [`succ_over_index_eq`]'s
/// cross-multiplication identity.
fn int_right_distrib(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let int = p.rat.int;
    let a_plus_b = d.iadd(a, b);
    let start = d.imul(a_plus_b, c);
    let step1 = d.lemma(int.mul_comm, &[a_plus_b, c]);
    let c_ab = d.imul(c, a_plus_b);
    let step2 = d.lemma(int.left_distrib, &[c, a, b]);
    let ca = d.imul(c, a);
    let cb = d.imul(c, b);
    let ca_cb = d.iadd(ca, cb);
    let ac = d.imul(a, c);
    let comm_ca = d.lemma(int.mul_comm, &[c, a]);
    let step3 = d.icongr(ca, ac, comm_ca, &|d, t| {
        let cb2 = d.imul(c, b);
        d.iadd(t, cb2)
    });
    let ac_cb = d.iadd(ac, cb);
    let bc = d.imul(b, c);
    let comm_cb = d.lemma(int.mul_comm, &[c, b]);
    let step4 = d.icongr(cb, bc, comm_cb, &|d, t| d.iadd(ac, t));
    let ac_bc = d.iadd(ac, bc);
    let (_, whole) = d.ichain(
        start,
        &[
            (c_ab, step1),
            (ca_cb, step2),
            (ac_cb, step3),
            (ac_bc, step4),
        ],
    );
    whole
}

/// `Rat.le x (Rat.add x y)`, from `Rat.le Rat.zero y` — `x <= x+y` via
/// `add_le_add x x 0 y (le_refl x) y_nonneg : x+0 <= x+y`, rewritten along
/// `add_zero`. (`x <= x+x` is the `y := x` instance.)
fn rat_le_add_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    y_nonneg: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero = rzero(d, rat);
    let refl_x = d.lemma(rat.le_refl, &[x]);
    let step = d.lemma(rat.add_le_add, &[x, x, zero, y, refl_x, y_nonneg]);
    let x_zero = radd(d, x, zero);
    let xy = radd(d, x, y);
    let az = d.lemma(rat.add_zero, &[x]);
    rat_eq_rewrite(d, x_zero, x, az, step, &|d, t| rle(d, rat, t, xy))
}

/// `Rat.le (Rat.add (a*a) (b*b)) ((a+b)*(a+b))`, given `0 <= a` and `0 <= b`.
///
/// `(a+b)^2 = a*a + a*b + b*a + b*b` (via [`rat_right_distrib`]/`left_distrib`),
/// and `a*a+b*b <= (a*a+b*b)+(a*b+b*a)` (the cross terms are non-negative) is
/// the same sum after a four-term reassociation.
fn sum_sq_le_sq_sum(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    a_nonneg: ExprId,
    b_nonneg: ExprId,
) -> ExprId {
    let rat = p.rat;
    let a_plus_b = radd(d, a, b);
    let start = rmul(d, a_plus_b, a_plus_b);

    // (a+b)*(a+b) = (a+b)*a + (a+b)*b
    let step1 = d.lemma(rat.left_distrib, &[a_plus_b, a, b]);
    let ab_a = rmul(d, a_plus_b, a);
    let ab_b = rmul(d, a_plus_b, b);
    let mid1 = radd(d, ab_a, ab_b);

    // (a+b)*a = a*a+b*a ; (a+b)*b = a*b+b*b
    let aa = rmul(d, a, a);
    let ba = rmul(d, b, a);
    let ab = rmul(d, a, b);
    let bb = rmul(d, b, b);
    let expand_a = rat_right_distrib(d, p, a, b, a);
    let expand_b = rat_right_distrib(d, p, a, b, b);
    let aa_ba = radd(d, aa, ba);
    let ab_bb = radd(d, ab, bb);
    let step2 = rcongr(d, ab_a, aa_ba, expand_a, &|d, t| radd(d, t, ab_b));
    let step3 = rcongr(d, ab_b, ab_bb, expand_b, &|d, t| radd(d, aa_ba, t));
    let mid2 = radd(d, aa_ba, ab_bb);
    let mid1b = radd(d, aa_ba, ab_b);

    let (_, whole_eq) = rchain(d, start, &[(mid1, step1), (mid1b, step2), (mid2, step3)]);
    // whole_eq : Eq Rat start mid2   -- mid2 = (a*a+b*a)+(a*b+b*b)

    // a*a+b*b <= mid2, via the 4-term regroup (a*a+b*b)+(b*a+a*b) = (a*a+b*a)+(a*b+b*b)
    // and `x <= x+y` for `y := b*a+a*b >= 0`.
    let base = radd(d, aa, bb);
    let cross = radd(d, ba, ab);
    let base_plus_cross = radd(d, base, cross);
    let cross_nonneg = {
        let m1 = d.lemma(rat.mul_nonneg, &[b, a, b_nonneg, a_nonneg]);
        let m2 = d.lemma(rat.mul_nonneg, &[a, b, a_nonneg, b_nonneg]);
        d.lemma(rat.add_nonneg, &[ba, ab, m1, m2])
    };
    let base_le = rat_le_add_nonneg(d, p, base, cross, cross_nonneg);
    // base_le : base <= base+cross

    // (a*a+b*b)+(b*a+a*b) = (a*a+b*a)+(a*b+b*b) : a 4-term regroup,
    // T1:=a*a, T2:=b*b, T3:=b*a, T4:=a*b throughout. Every intermediate sum
    // is bound to its own name first -- `radd`/`rsymm`/`rcongr` all take
    // `&mut IntDev` explicitly, and this kernel's helpers (unlike ordinary
    // method chains) get no two-phase-borrow leniency for a *reference*
    // parameter, so nesting a second such call inside the first's argument
    // list does not borrow-check.
    let regroup = {
        let t1 = aa;
        let t2 = bb;
        let t3 = ba;
        let t4 = ab;

        let t12 = radd(d, t1, t2);
        let t34 = radd(d, t3, t4);
        let lhs = radd(d, t12, t34);
        let t2_t34 = radd(d, t2, t34);
        let s1 = radd(d, t1, t2_t34);
        // hop1 : (t1+t2)+t34 = t1+(t2+t34)
        let hop1 = d.lemma(rat.add_assoc, &[t1, t2, t34]);

        let t23 = radd(d, t2, t3);
        let t23_t4 = radd(d, t23, t4);
        let inner_assoc = d.lemma(rat.add_assoc, &[t2, t3, t4]);
        // inner_assoc : (t2+t3)+t4 = t2+(t3+t4) = t23_t4 = t2_t34
        let inner_rev = rsymm(d, t23_t4, t2_t34, inner_assoc);
        // inner_rev : t2_t34 = t23_t4
        let s2 = radd(d, t1, t23_t4);
        let hop2 = rcongr(d, t2_t34, t23_t4, inner_rev, &|d, t| radd(d, t1, t));
        // hop2 : s1 = s2

        let t32 = radd(d, t3, t2);
        let comm23 = d.lemma(rat.add_comm, &[t2, t3]);
        // comm23 : t2+t3 = t3+t2, i.e. t23 = t32
        let t32_t4 = radd(d, t32, t4);
        let lift3 = rcongr(d, t23, t32, comm23, &|d, t| radd(d, t, t4));
        // lift3 : t23_t4 = t32_t4
        let s3 = radd(d, t1, t32_t4);
        let hop3 = rcongr(d, t23_t4, t32_t4, lift3, &|d, t| radd(d, t1, t));
        // hop3 : s2 = s3

        let t24 = radd(d, t2, t4);
        let t3_t24 = radd(d, t3, t24);
        let inner_assoc2 = d.lemma(rat.add_assoc, &[t3, t2, t4]);
        // inner_assoc2 : (t3+t2)+t4 = t3+(t2+t4), i.e. t32_t4 = t3_t24
        let s4 = radd(d, t1, t3_t24);
        let hop4 = rcongr(d, t32_t4, t3_t24, inner_assoc2, &|d, t| radd(d, t1, t));
        // hop4 : s3 = s4

        let t13 = radd(d, t1, t3);
        let a135 = d.lemma(rat.add_assoc, &[t1, t3, t24]);
        // a135 : (t1+t3)+t24 = t1+(t3+t24), i.e. Eq s5 s4
        let s5 = radd(d, t13, t24);
        let hop5 = rsymm(d, s5, s4, a135);
        // hop5 : s4 = s5

        let t42 = radd(d, t4, t2);
        let comm24 = d.lemma(rat.add_comm, &[t2, t4]);
        // comm24 : t2+t4 = t4+t2, i.e. t24 = t42
        let s6 = radd(d, t13, t42);
        let hop6 = rcongr(d, t24, t42, comm24, &|d, t| radd(d, t13, t));
        // hop6 : s5 = s6

        let (_, regroup_eq) = rchain(
            d,
            lhs,
            &[
                (s1, hop1),
                (s2, hop2),
                (s3, hop3),
                (s4, hop4),
                (s5, hop5),
                (s6, hop6),
            ],
        );
        regroup_eq
    };
    // regroup : Eq Rat (base+cross) mid2

    let base_le_mid2 = rat_eq_rewrite(d, base_plus_cross, mid2, regroup, base_le, &|d, t| {
        rle(d, rat, base, t)
    });
    // base_le_mid2 : base <= mid2

    let whole_eq_rev = rsymm(d, start, mid2, whole_eq);
    rat_eq_rewrite(d, mid2, start, whole_eq_rev, base_le_mid2, &|d, t| {
        rle(d, rat, base, t)
    })
}

/// `Rat.le Rat.zero (Rat.normalize (Int.ofNat k) den_nat h)` — normalizing a
/// non-negative-numerator fraction over a positive denominator stays
/// non-negative.
///
/// Via `Rat.normalize_cross` (`num(normalize k den h)*ofNat(den_nat) =
/// ofNat(k)*ofNat(den(normalize k den h))`, whose right side is a product of
/// two `ofNat`s, hence non-negative), then
/// `Rat.int_le_of_mul_le_mul_right` cancelling the positive `ofNat(den_nat)`
/// factor to recover `0 <= num(normalize k den_nat h)`, then
/// `Rat.nonneg_of_int_nonneg`.
fn normalize_of_nat_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    den_nat: ExprId,
    h: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = p.rat.int.nat;
    let k_int = d.of_nat(k);
    let q = normalize(d, k_int, den_nat, h);
    let cross = d.lemma(rat.normalize_cross, &[k_int, den_nat, h]);
    // cross : Eq Int (num(q)*ofNat(den_nat)) (k_int*ofNat(den q))
    let dq = den(d, q);
    let dq_z = den_z(d, q);
    let den_nat_z = d.of_nat(den_nat);
    let nq = num(d, q);
    let nq_dnz = d.imul(nq, den_nat_z);
    let k_dqz = d.imul(k_int, dq_z);

    let zero_le_k = d.lemma(nat.zero_le, &[k]); // used as Int.le 0 k_int via defeq
    let zero_le_dqz = d.lemma(nat.zero_le, &[dq]); // used as Int.le 0 dq_z via defeq
    let rhs_nonneg = d.lemma(rat.int.mul_nonneg, &[k_int, dq_z, zero_le_k, zero_le_dqz]);
    // rhs_nonneg : Int.le 0 (k_int*dq_z)

    let cross_rev = d.isymm(nq_dnz, k_dqz, cross);
    let zero_nat = d.zero();
    let zero_int = d.of_nat(zero_nat);
    let lhs_nonneg = {
        let motive = d.ieq_motive(k_dqz, &|d, t| d.ile(zero_int, t));
        d.itransport(k_dqz, motive, rhs_nonneg, nq_dnz, cross_rev)
    };
    // lhs_nonneg : Int.le 0 (nq*den_nat_z)

    let zero_mul_dnz = d.imul(zero_int, den_nat_z);
    let zero_mul_eq = {
        let comm = d.lemma(rat.int.mul_comm, &[zero_int, den_nat_z]);
        let dz_zero = d.imul(den_nat_z, zero_int);
        let mz = d.lemma(rat.int.mul_zero, &[den_nat_z]);
        let (_, e) = d.ichain(zero_mul_dnz, &[(dz_zero, comm), (zero_int, mz)]);
        e
    };
    // zero_mul_eq : Eq Int zero_mul_dnz zero_int
    let scaled_zero_le = {
        let rev = d.isymm(zero_mul_dnz, zero_int, zero_mul_eq);
        let motive = d.ieq_motive(zero_int, &|d, t| d.ile(t, nq_dnz));
        d.itransport(zero_int, motive, lhs_nonneg, zero_mul_dnz, rev)
    };
    // scaled_zero_le : Int.le (0*den_nat_z) (nq*den_nat_z)
    let cancel = d.lemma(
        rat.int_le_of_mul_le_mul_right,
        &[zero_int, nq, den_nat, h, scaled_zero_le],
    );
    // cancel : Int.le 0 nq
    d.lemma(rat.nonneg_of_int_nonneg, &[q, cancel])
}

/// `Eq Rat (normalize (Int.ofNat (Nat.succ s)) (Nat.succ idx) pos)
///         (Rat.add (normalize (Int.ofNat s) (Nat.succ idx) pos) (natDivSucc 1 idx))`
///
/// The next `sqrtApprox`-shaped candidate up is exactly the current one plus
/// one unit at the same denominator. Both `normalize`s share denominator
/// `dd := succ idx`, so `Rat.normalize_add_normalize` lands the sum at
/// `normalize(s*dd+1*dd, dd*dd, _)`, and `Rat.normalize_congr` reads that
/// back to `normalize(succ s, dd, _)` via the ring identity `(s*dd+1*dd)*dd =
/// (succ s)*(dd*dd)` — built entirely from `int_right_distrib`/`mul_assoc`,
/// exploiting that `Int.mul`'s `ofNat`/`ofNat` case makes `dd_int*dd_int` and
/// `Int.ofNat(dd*dd)` interchangeable by computation (two ι-steps on the
/// *integer* constructor, regardless of whether the underlying `Nat` product
/// itself reduces further), and that `succ_s_int` and `s_int+one_int` are
/// likewise interchangeable (`Nat.add`'s recursion on the literal `1` on the
/// right is not stuck even for symbolic `s`).
fn succ_over_index_eq(d: &mut IntDev<'_>, p: CRealPrelude, s: ExprId, idx: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = p.rat.int.nat;
    let dd = d.succ(idx);
    let pos = one_le_succ(d, idx);
    let j = NatOps::mul(d, dd, dd);
    let pos_j = d.lemma(nat.one_le_mul, &[dd, dd, pos, pos]);

    let s_int = d.of_nat(s);
    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);
    let succ_s = d.succ(s);
    let succ_s_int = d.of_nat(succ_s);
    let dd_int = d.of_nat(dd);
    let j_int = d.of_nat(j);

    let num_val = {
        let a = d.imul(s_int, dd_int);
        let b = d.imul(one_int, dd_int);
        d.iadd(a, b)
    };

    // cross : Eq Int (succ_s_int * j_int) (num_val * dd_int)
    let cross = {
        let s_j = d.imul(s_int, j_int);
        let one_j = d.imul(one_int, j_int);
        let s_j_plus_one_j = d.iadd(s_j, one_j);

        // Left chain: succ_s_int*j_int -[defeq]-> (s_int+one_int)*j_int
        //                                -[int_right_distrib]-> s_int*j_int+one_int*j_int
        let start_left = d.imul(succ_s_int, j_int);
        let s_plus_one = d.iadd(s_int, one_int);
        let free1 = d.irefl(start_left);
        let mid_left = d.imul(s_plus_one, j_int);
        let distrib_left = int_right_distrib(d, p, s_int, one_int, j_int);
        let (_, left_eq) = d.ichain(
            start_left,
            &[(mid_left, free1), (s_j_plus_one_j, distrib_left)],
        );

        // Right chain: num_val*dd_int -[int_right_distrib]-> (s*dd)*dd + (1*dd)*dd
        //                             -[mul_assoc, defeq to j_int]-> s*j_int + (1*dd)*dd
        //                             -[mul_assoc, defeq to j_int]-> s*j_int + 1*j_int
        let start_right = d.imul(num_val, dd_int);
        let s_dd = d.imul(s_int, dd_int);
        let one_dd = d.imul(one_int, dd_int);
        let a_dd = d.imul(s_dd, dd_int);
        let b_dd = d.imul(one_dd, dd_int);
        let sum_dd = d.iadd(a_dd, b_dd);
        let distrib_right = int_right_distrib(d, p, s_dd, one_dd, dd_int);
        let assoc_a = d.lemma(rat.int.mul_assoc, &[s_int, dd_int, dd_int]);
        let mid_r2 = d.iadd(s_j, b_dd);
        let step_a = d.icongr(a_dd, s_j, assoc_a, &|d, t| {
            let bd = d.imul(one_dd, dd_int);
            d.iadd(t, bd)
        });
        let assoc_b = d.lemma(rat.int.mul_assoc, &[one_int, dd_int, dd_int]);
        let step_b = d.icongr(b_dd, one_j, assoc_b, &|d, t| d.iadd(s_j, t));
        let (_, right_eq) = d.ichain(
            start_right,
            &[
                (sum_dd, distrib_right),
                (mid_r2, step_a),
                (s_j_plus_one_j, step_b),
            ],
        );

        let right_eq_rev = d.isymm(start_right, s_j_plus_one_j, right_eq);
        let (_, whole) = d.ichain(
            start_left,
            &[(s_j_plus_one_j, left_eq), (start_right, right_eq_rev)],
        );
        whole
    };

    let congr_step = d.lemma(
        rat.normalize_congr,
        &[succ_s_int, dd, pos, num_val, j, pos_j, cross],
    );
    // congr_step : Eq Rat (normalize succ_s_int dd pos) (normalize num_val j pos_j)

    let add_normalize = d.lemma(
        rat.normalize_add_normalize,
        &[s_int, dd, pos, one_int, dd, pos],
    );
    // add_normalize : Eq Rat (normalize s_int dd pos + normalize one_int dd pos) (normalize num_val j _)

    let lhs = normalize(d, succ_s_int, dd, pos);
    let rhs_normalize = normalize(d, num_val, j, pos_j);
    let left_summand = normalize(d, s_int, dd, pos);
    let right_summand_n = normalize(d, one_int, dd, pos);
    let sum_n = radd(d, left_summand, right_summand_n);
    let add_normalize_rev = rsymm(d, sum_n, rhs_normalize, add_normalize);

    let (_, whole) = rchain(
        d,
        lhs,
        &[(rhs_normalize, congr_step), (sum_n, add_normalize_rev)],
    );
    // whole : Eq Rat lhs sum_n, and `sum_n` is defeq
    // `radd(left_summand, div_succ(d,p,1,idx))` (`natDivSucc`'s own
    // unfolding), which is what the caller's declared type actually names.
    whole
}

/// `Rat.le (natDivSucc 1 ((succ idx)*(succ idx))) (Rat.mul (natDivSucc 1 idx) (natDivSucc 1 idx))`
///
/// Deepening the sample index from `dd := succ idx` to `dd*dd` shrinks the
/// bound past its own square: `1/(dd^2+1) <= 1/dd^2`. Via
/// `Rat.natDivSucc_antitone` at `(pred(dd^2), dd^2)` — `dd^2 >= 1`, via
/// `Nat.one_le_mul` — plus the same `j = succ(pred j)` bridge
/// [`one_le_implies_succ_pred`] supplies, read into `Rat` by
/// cross-multiplication (`Rat.normalize_congr`) rather than a dependent
/// rewrite, since `normalize`'s own third argument is itself a proof
/// obligation and no motive can abstract over its index the naive way.
fn div_succ_sq_bound(d: &mut IntDev<'_>, p: CRealPrelude, idx: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = p.rat.int.nat;
    let dd = d.succ(idx);
    let pos = one_le_succ(d, idx);
    let j = NatOps::mul(d, dd, dd);
    let pos_j = d.lemma(nat.one_le_mul, &[dd, dd, pos, pos]);

    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);

    let pred_j = d.pred(j);
    let pred_le = d.lemma(nat.pred_le, &[j]);
    let antitone = d.lemma(rat.nat_div_succ_antitone, &[pred_j, j, pred_le]);
    // antitone : Rat.le (natDivSucc 1 j) (natDivSucc 1 pred_j)

    let succ_pred_fn = one_le_implies_succ_pred(d, p, j);
    let j_eq_succ_pred = d.apply(succ_pred_fn, &[pos_j]);
    // j_eq_succ_pred : Eq Nat j (succ pred_j)
    let succ_pred = d.succ(pred_j);
    let pos_succ_pred = one_le_succ(d, pred_j);

    let int_eq = d.nat_eq_to_int(j, succ_pred, j_eq_succ_pred, &|d, t| {
        let ot = d.of_nat(t);
        d.imul(one_int, ot)
    });
    // int_eq : Eq Int (one_int * ofNat j) (one_int * ofNat succ_pred)

    let congr = d.lemma(
        rat.normalize_congr,
        &[one_int, j, pos_j, one_int, succ_pred, pos_succ_pred, int_eq],
    );
    // congr : Eq Rat (normalize one_int j pos_j) (normalize one_int succ_pred pos_succ_pred)
    //       = Eq Rat normalize_j target_pred
    let normalize_j = normalize(d, one_int, j, pos_j);
    let target_pred = div_succ(d, p, 1, pred_j);
    let congr_rev = rsymm(d, normalize_j, target_pred, congr);
    // congr_rev : Eq Rat target_pred normalize_j

    let bound_at_j = div_succ(d, p, 1, j);
    let step1 = rat_eq_rewrite(d, target_pred, normalize_j, congr_rev, antitone, &|d, t| {
        rle(d, rat, bound_at_j, t)
    });
    // step1 : Rat.le bound_at_j normalize_j

    let mul_normalize = d.lemma(
        rat.normalize_mul_normalize,
        &[one_int, dd, pos, one_int, dd, pos],
    );
    // mul_normalize : Eq Rat (normalize(one_int,dd,pos)*normalize(one_int,dd,pos))
    //                        (normalize(one_int*one_int, j, _))
    let sq = {
        let d1 = div_succ(d, p, 1, idx);
        rmul(d, d1, d1)
    };
    // mul_normalize's actual type is `Eq (d1*d1) (normalize(one*one,j,_))` up
    // to defeq (`normalize(one_int,dd,pos)` unfolds `nat_div_succ 1 idx`, and
    // `one_int*one_int` unfolds `one_int`, same denominator `j`,
    // proof-irrelevant) -- i.e. `Eq sq normalize_j`, not the other way round.
    let mul_normalize_rev = rsymm(d, sq, normalize_j, mul_normalize);
    // mul_normalize_rev : Eq Rat normalize_j sq

    rat_eq_rewrite(d, normalize_j, sq, mul_normalize_rev, step1, &|d, t| {
        rle(d, rat, bound_at_j, t)
    })
}

/// `Eq Rat (Rat.add (natDivSucc 1 idx) (natDivSucc 1 idx)) (natDivSucc 2 idx)`
/// — `Rat.natDivSucc_add` at `(1,1,idx)`, `1+1` reducing to the literal `2`
/// by pure computation.
fn double_div_succ_eq(d: &mut IntDev<'_>, p: CRealPrelude, idx: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, idx])
}

/// `Rat.le (Rat.sub (sqrtApprox x a_idx) (sqrtApprox x b_idx))
///         (Rat.add (natDivSucc 1 b_idx) (Rat.add (natDivSucc 1 a_idx) (natDivSucc 1 b_idx)))`
///
/// The cross-index squeeze, one direction: `u_a := sqrtApprox x a_idx`,
/// `u_b := sqrtApprox x b_idx`, `q_a`/`q_b` their clamped samples at
/// `j_a := (a_idx+1)^2`/`j_b := (b_idx+1)^2`.
///
/// - `u_a^2 <= q_a` ([`CRealPrelude::sqrt_approx_sq_bracket`]'s lower half at
///   `a_idx`).
/// - `q_a <= q_b + modulus(j_a,j_b)` (`Rat.sub_max_le`, `max` is 1-Lipschitz,
///   applied to `x`'s own regularity at `(j_a,j_b)` and the trivial
///   `0-0<=modulus`).
/// - `q_b < u_b1^2` ([`CRealPrelude::sqrt_approx_sq_bracket`]'s upper half at
///   `b_idx`, `u_b1` the next candidate up).
/// - `modulus(j_a,j_b) <= E*E` (`E := natDivSucc 1 a_idx + natDivSucc 1
///   b_idx`), via [`div_succ_sq_bound`] at each index plus
///   [`sum_sq_le_sq_sum`].
/// - hence `u_a^2 <= u_b1^2 + E*E <= (u_b1+E)^2` (the second step is
///   [`sum_sq_le_sq_sum`] again, at `(u_b1, E)`), and
///   [`CRealPrelude::rat_sq_le`] (division-free) gives `u_a <= u_b1+E`.
/// - `u_b1 = u_b + natDivSucc 1 b_idx` ([`succ_over_index_eq`]), so
///   `u_a - u_b <= natDivSucc 1 b_idx + E`.
#[allow(clippy::too_many_lines)]
fn one_sided_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    a_idx: ExprId,
    b_idx: ExprId,
) -> ExprId {
    let rat = p.rat;
    let one_nat_lit = d.num(1);

    // --- rebuild both brackets' shared setup, matching `sqrt_approx_sq_bracket`. ---
    // `sqrt_approx_sq_bracket`'s own conclusion is stated with the SQUARE
    // COLLAPSED into a single `Rat.normalize` over the sample index `j`
    // (`rep_s`/`rep_s1` in that declaration's own naming) -- `Rat.mul
    // (normalize s dd _) (normalize s dd _)` is only PROPOSITIONALLY equal to
    // that, via `Rat.normalize_mul_normalize`, not definitionally, so the
    // bracket must be projected at the collapsed shape and then bridged.
    let bracket_setup = |d: &mut IntDev<'_>,
                         n: ExprId|
     -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
        // returns (j, q, s, s1, dd, pos, j_pos).
        let dd = d.succ(n);
        let pos = one_le_succ(d, n);
        let j = NatOps::mul(d, dd, dd);
        let sample_n = sample(d, p, x, j);
        let zero_rat = rzero(d, rat);
        let q = d.const_app(rat.max, &[sample_n, zero_rat]);
        let q_nonneg = d.lemma(rat.le_max_right, &[sample_n, zero_rat]);
        let num_q_nonneg = d.lemma(rat.int_nonneg_of_nonneg, &[q, q_nonneg]);
        let num_q = num(d, q);
        let a = d.const_app(rat.int.nat_abs, &[num_q]);
        let b = den(d, q);
        let scaled = NatOps::mul(d, a, j);
        let k = NatOps::div(d, scaled, b);
        let s = d.const_app(p.nat_sqrt, &[k]);
        let s1 = d.succ(s);
        let nat = p.rat.int.nat;
        let j_pos = d.lemma(nat.one_le_mul, &[dd, dd, pos, pos]);
        let _ = num_q_nonneg;
        (j, q, s, s1, dd, pos, j_pos)
    };

    let bracket_a = d.lemma(p.sqrt_approx_sq_bracket, &[x, a_idx]);
    let bracket_b = d.lemma(p.sqrt_approx_sq_bracket, &[x, b_idx]);

    let (j_a, q_a, s_a, s1_a, dd_a, pos_a, j_pos_a) = bracket_setup(d, a_idx);
    let (j_b, q_b, s_b, s1_b, dd_b, pos_b, j_pos_b) = bracket_setup(d, b_idx);

    let s_a_int = d.of_nat(s_a);
    let u_a = normalize(d, s_a_int, dd_a, pos_a);
    let u_a_sq = rmul(d, u_a, u_a);
    let s1_a_int = d.of_nat(s1_a);

    let s_b_int = d.of_nat(s_b);
    let u_b = normalize(d, s_b_int, dd_b, pos_b);
    let s1_b_int = d.of_nat(s1_b);
    let u_b1 = normalize(d, s1_b_int, dd_b, pos_b);
    let u_b1_sq = rmul(d, u_b1, u_b1);

    // The bracket's own collapsed forms: rep_s/rep_s1 at index a, rep_s/rep_s1
    // at index b (this file's own naming from `declare_sqrt_approx_sq_bracket`).
    let ssz_a = d.imul(s_a_int, s_a_int);
    let rep_s_a = normalize(d, ssz_a, j_a, j_pos_a);
    let s1sq_a = d.imul(s1_a_int, s1_a_int);
    let rep_s1_a = normalize(d, s1sq_a, j_a, j_pos_a);

    let ssz_b = d.imul(s_b_int, s_b_int);
    let rep_s_b = normalize(d, ssz_b, j_b, j_pos_b);
    let s1sq_b = d.imul(s1_b_int, s1_b_int);
    let rep_s1_b = normalize(d, s1sq_b, j_b, j_pos_b);

    let lower_a_ty = rle(d, rat, rep_s_a, q_a);
    let upper_a_ty = rlt(d, rat, q_a, rep_s1_a);
    let lower_a_raw = d.and_left(lower_a_ty, upper_a_ty, bracket_a);
    // lower_a_raw : Rat.le rep_s_a q_a
    let mul_normalize_a = d.lemma(
        rat.normalize_mul_normalize,
        &[s_a_int, dd_a, pos_a, s_a_int, dd_a, pos_a],
    );
    // mul_normalize_a : Eq (u_a*u_a) rep_s_a   (denominator dd_a*dd_a defeq j_a)
    let mul_normalize_a_rev = rsymm(d, u_a_sq, rep_s_a, mul_normalize_a);
    let lower_a = rat_eq_rewrite(
        d,
        rep_s_a,
        u_a_sq,
        mul_normalize_a_rev,
        lower_a_raw,
        &|d, t| rle(d, rat, t, q_a),
    );
    // lower_a : Rat.le u_a_sq q_a

    let lower_b_ty = rle(d, rat, rep_s_b, q_b);
    let upper_b_ty = rlt(d, rat, q_b, rep_s1_b);
    let upper_b_raw = d.and_right(lower_b_ty, upper_b_ty, bracket_b);
    // upper_b_raw : Rat.lt q_b rep_s1_b
    let mul_normalize_b1 = d.lemma(
        rat.normalize_mul_normalize,
        &[s1_b_int, dd_b, pos_b, s1_b_int, dd_b, pos_b],
    );
    // mul_normalize_b1 : Eq (u_b1*u_b1) rep_s1_b
    let mul_normalize_b1_rev = rsymm(d, u_b1_sq, rep_s1_b, mul_normalize_b1);
    let upper_b = rat_eq_rewrite(
        d,
        rep_s1_b,
        u_b1_sq,
        mul_normalize_b1_rev,
        upper_b_raw,
        &|d, t| rlt(d, rat, q_b, t),
    );
    // upper_b : Rat.lt q_b u_b1_sq
    let upper_b_le = d.lemma(rat.le_of_lt, &[q_b, u_b1_sq, upper_b]);
    // upper_b_le : q_b <= u_b1_sq

    // --- delta := q_a - q_b <= modulus(j_a, j_b), via sub_max_le. ---
    let modulus_ab = modulus(d, p, j_a, j_b);
    let x_reg = d.lemma(p.regular, &[x, j_a, j_b]);
    // x_reg : Within (seq x j_a - seq x j_b) modulus_ab
    let sample_ja = sample(d, p, x, j_a);
    let sample_jb = sample(d, p, x, j_b);
    let sample_diff = rsub(d, rat, sample_ja, sample_jb);
    let (_reg_lower, reg_upper) = halves(d, p, sample_diff, modulus_ab, x_reg);
    // reg_upper : Rat.le (seq x j_a - seq x j_b) modulus_ab

    let zero_rat = rzero(d, rat);
    let div_succ_ja = div_succ(d, p, 1, j_a);
    let div_succ_jb = div_succ(d, p, 1, j_b);
    let zero_sub_zero_le = {
        let zero_sub_zero = rsub(d, rat, zero_rat, zero_rat);
        let sub_self = d.lemma(rat.sub_self, &[zero_rat]);
        // sub_self : Rat.sub zero zero = zero
        let modulus_nonneg = {
            let m1 = d.lemma(rat.zero_le_nat_div_succ, &[one_nat_lit, j_a]);
            let m2 = d.lemma(rat.zero_le_nat_div_succ, &[one_nat_lit, j_b]);
            d.lemma(rat.add_nonneg, &[div_succ_ja, div_succ_jb, m1, m2])
        };
        rat_eq_rewrite(
            d,
            zero_sub_zero,
            zero_rat,
            sub_self,
            modulus_nonneg,
            &|d, t| rle(d, rat, t, modulus_ab),
        )
    };
    // zero_sub_zero_le : Rat.le (Rat.sub zero zero) modulus_ab
    let sub_max = d.lemma(
        rat.sub_max_le,
        &[
            sample_ja,
            zero_rat,
            sample_jb,
            zero_rat,
            modulus_ab,
            reg_upper,
            zero_sub_zero_le,
        ],
    );
    // sub_max : Rat.le (Rat.sub q_a q_b) modulus_ab

    let q_a_le = d.lemma(rat.le_of_sub_le, &[q_a, q_b, modulus_ab, sub_max]);
    // q_a_le : q_a <= q_b + modulus_ab

    let qb_plus_mod = radd(d, q_b, modulus_ab);
    let step5 = d.lemma(rat.le_trans, &[u_a_sq, q_a, qb_plus_mod, lower_a, q_a_le]);
    // step5 : u_a_sq <= q_b + modulus_ab

    let refl_mod = d.lemma(rat.le_refl, &[modulus_ab]);
    let step7 = d.lemma(
        rat.add_le_add,
        &[q_b, u_b1_sq, modulus_ab, modulus_ab, upper_b_le, refl_mod],
    );
    // step7 : q_b+modulus_ab <= u_b1_sq+modulus_ab

    let ub1sq_plus_mod = radd(d, u_b1_sq, modulus_ab);
    let step8 = d.lemma(
        rat.le_trans,
        &[u_a_sq, qb_plus_mod, ub1sq_plus_mod, step5, step7],
    );
    // step8 : u_a_sq <= u_b1_sq + modulus_ab

    // --- modulus_ab <= E*E. ---
    let one_a = div_succ(d, p, 1, a_idx);
    let one_b = div_succ(d, p, 1, b_idx);
    let e = radd(d, one_a, one_b);
    let ee = rmul(d, e, e);
    let a_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat_lit, a_idx]);
    let b_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat_lit, b_idx]);

    let bound_a = div_succ_sq_bound(d, p, a_idx);
    let bound_b = div_succ_sq_bound(d, p, b_idx);
    let aa_sq = rmul(d, one_a, one_a);
    let bb_sq = rmul(d, one_b, one_b);
    let aa_plus_bb = radd(d, aa_sq, bb_sq);
    let sum_bounds = d.lemma(
        rat.add_le_add,
        &[div_succ_ja, aa_sq, div_succ_jb, bb_sq, bound_a, bound_b],
    );
    // sum_bounds : modulus_ab <= (A*A)+(B*B)
    let sq_sum_le = sum_sq_le_sq_sum(d, p, one_a, one_b, a_nonneg, b_nonneg);
    // sq_sum_le : (A*A)+(B*B) <= (A+B)*(A+B) = e*e
    let mod_le_esq = d.lemma(
        rat.le_trans,
        &[modulus_ab, aa_plus_bb, ee, sum_bounds, sq_sum_le],
    );
    // mod_le_esq : modulus_ab <= e*e

    let refl_ubsq = d.lemma(rat.le_refl, &[u_b1_sq]);
    let step10 = d.lemma(
        rat.add_le_add,
        &[u_b1_sq, u_b1_sq, modulus_ab, ee, refl_ubsq, mod_le_esq],
    );
    // step10 : u_b1_sq + modulus_ab <= u_b1_sq + e*e

    let ub1sq_plus_ee = radd(d, u_b1_sq, ee);
    let step11 = d.lemma(
        rat.le_trans,
        &[u_a_sq, ub1sq_plus_mod, ub1sq_plus_ee, step8, step10],
    );
    // step11 : u_a_sq <= u_b1_sq + e*e

    // --- u_b1_sq + e*e <= (u_b1+e)*(u_b1+e). ---
    let u_b1_nonneg = normalize_of_nat_nonneg(d, p, s1_b, dd_b, pos_b);
    let e_nonneg = d.lemma(rat.add_nonneg, &[one_a, one_b, a_nonneg, b_nonneg]);
    let step12 = sum_sq_le_sq_sum(d, p, u_b1, e, u_b1_nonneg, e_nonneg);
    // step12 : u_b1_sq + e*e <= (u_b1+e)*(u_b1+e)

    let ub1_plus_e = radd(d, u_b1, e);
    let ub1_plus_e_sq = rmul(d, ub1_plus_e, ub1_plus_e);
    let step13 = d.lemma(
        rat.le_trans,
        &[u_a_sq, ub1sq_plus_ee, ub1_plus_e_sq, step11, step12],
    );
    // step13 : u_a_sq <= (u_b1+e)*(u_b1+e)

    let target_nonneg = d.lemma(rat.add_nonneg, &[u_b1, e, u_b1_nonneg, e_nonneg]);
    let squeeze = d.lemma(p.rat_sq_le, &[u_a, ub1_plus_e, step13, target_nonneg]);
    // squeeze : u_a <= u_b1+e

    // --- u_b1 = u_b + natDivSucc 1 b_idx, so u_a - u_b <= natDivSucc 1 b_idx + e. ---
    let succ_eq = succ_over_index_eq(d, p, s_b, b_idx);
    // succ_eq : Eq Rat u_b1 (Rat.add u_b (natDivSucc 1 b_idx))
    let u_b_plus_oneb = radd(d, u_b, one_b);
    let target_rewritten = rat_eq_rewrite(d, u_b1, u_b_plus_oneb, succ_eq, squeeze, &|d, t| {
        let bound = radd(d, t, e);
        rle(d, rat, u_a, bound)
    });
    // target_rewritten : u_a <= (u_b + natDivSucc 1 b_idx) + e

    // Reassociate the RHS to `u_b + (natDivSucc 1 b_idx + e)` so `sub_le_of_le` applies.
    let assoc = d.lemma(rat.add_assoc, &[u_b, one_b, e]);
    let u_b_plus_oneb_plus_e = radd(d, u_b_plus_oneb, e);
    let oneb_plus_e = radd(d, one_b, e);
    let u_b_plus_onebpluse = radd(d, u_b, oneb_plus_e);
    let rebound = rat_eq_rewrite(
        d,
        u_b_plus_oneb_plus_e,
        u_b_plus_onebpluse,
        assoc,
        target_rewritten,
        &|d, t| rle(d, rat, u_a, t),
    );
    // rebound : u_a <= u_b + (natDivSucc 1 b_idx + e)

    d.lemma(rat.sub_le_of_le, &[u_a, u_b, oneb_plus_e, rebound])
    // : u_a - u_b <= natDivSucc 1 b_idx + e
}

/// `Rat.le (Rat.add (natDivSucc 1 b_idx) (Rat.add (natDivSucc 1 a_idx) (natDivSucc 1 b_idx)))
///         (Rat.add (Rat.add (natDivSucc 1 a_idx) (natDivSucc 1 a_idx)) (Rat.add (natDivSucc 1 b_idx) (natDivSucc 1 b_idx)))`
///
/// [`one_sided_bound`]'s raw bound is at most `2*natDivSucc(1,a_idx) +
/// 2*natDivSucc(1,b_idx)` — [`double_div_succ_eq`] reads the right side back
/// to `natDivSucc 2 a_idx + natDivSucc 2 b_idx`, the exact `KRegular`
/// modulus at `c=1`.
fn raw_bound_le_double(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_idx: ExprId,
    b_idx: ExprId,
) -> ExprId {
    let rat = p.rat;
    let one_nat_lit = d.num(1);
    let x = div_succ(d, p, 1, a_idx);
    let y = div_succ(d, p, 1, b_idx);
    let x_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat_lit, a_idx]);

    let x_plus_y = radd(d, x, y);
    let raw = radd(d, y, x_plus_y);
    let y_plus_x = radd(d, y, x);
    let y_plus_x_plus_y = radd(d, y_plus_x, y);
    let x_plus_y_plus_y = radd(d, x_plus_y, y);

    // raw = (y+x)+y
    let assoc1 = d.lemma(rat.add_assoc, &[y, x, y]); // (y+x)+y = y+(x+y) = raw
    let assoc1_rev = rsymm(d, y_plus_x_plus_y, raw, assoc1);
    // (y+x)+y = (x+y)+y
    let comm1 = d.lemma(rat.add_comm, &[y, x]);
    let step2 = rcongr(d, y_plus_x, x_plus_y, comm1, &|d, t| radd(d, t, y));
    // (x+y)+y = x+(y+y)
    let y_plus_y = radd(d, y, y);
    let step3 = d.lemma(rat.add_assoc, &[x, y, y]);
    let x_plus_yy = radd(d, x, y_plus_y);

    let (_, whole_eq) = rchain(
        d,
        raw,
        &[
            (y_plus_x_plus_y, assoc1_rev),
            (x_plus_y_plus_y, step2),
            (x_plus_yy, step3),
        ],
    );
    // whole_eq : raw = x+(y+y)

    let x_le_xx = rat_le_add_nonneg(d, p, x, x, x_nonneg);
    let xx = radd(d, x, x);
    let refl_yy = d.lemma(rat.le_refl, &[y_plus_y]);
    let le_step = d.lemma(
        rat.add_le_add,
        &[x, xx, y_plus_y, y_plus_y, x_le_xx, refl_yy],
    );
    // le_step : x+(y+y) <= (x+x)+(y+y)

    let target = radd(d, xx, y_plus_y);
    let whole_eq_rev = rsymm(d, raw, x_plus_yy, whole_eq);
    rat_eq_rewrite(d, x_plus_yy, raw, whole_eq_rev, le_step, &|d, t| {
        rle(d, rat, t, target)
    })
    // : raw <= (x+x)+(y+y)
}

/// `CReal.sqrtApproxKRegular : ∀ x, KRegular (sqrtApprox x) 1`.
///
/// Both directions of `Within` follow the same [`one_sided_bound`] argument
/// with the two indices swapped, widened to the exact modulus by
/// [`raw_bound_le_double`] and [`double_div_succ_eq`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_sqrt_approx_kregular(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sqrt_approx_x_m = {
        let f = d.const_app(p.sqrt_approx, &[x]);
        d.apply(f, &[m])
    };
    let sqrt_approx_x_n = {
        let f = d.const_app(p.sqrt_approx, &[x]);
        d.apply(f, &[n])
    };

    let diff = rsub(d, rat, sqrt_approx_x_m, sqrt_approx_x_n);
    let div2_m = div_succ(d, p, 2, m);
    let div2_n = div_succ(d, p, 2, n);
    let target = radd(d, div2_m, div2_n);
    let claim = within(d, p, diff, target);

    // `widen_direction(a_idx, b_idx)` proves `Rat.le (sqrtApprox x a_idx -
    // sqrtApprox x b_idx) (natDivSucc 2 a_idx + natDivSucc 2 b_idx)`, i.e.
    // the KRegular target read in the `(a_idx, b_idx)` order (not yet
    // `add_comm`-matched to the DECLARED `target`, which is fixed at `(m,
    // n)`).
    let widen_direction = |d: &mut IntDev<'_>, a_idx: ExprId, b_idx: ExprId| -> (ExprId, ExprId) {
        let diff_ab = {
            let fa = d.const_app(p.sqrt_approx, &[x]);
            let ua = d.apply(fa, &[a_idx]);
            let fb = d.const_app(p.sqrt_approx, &[x]);
            let ub = d.apply(fb, &[b_idx]);
            rsub(d, rat, ua, ub)
        };
        let one_a = div_succ(d, p, 1, a_idx);
        let one_b = div_succ(d, p, 1, b_idx);
        let two_a = div_succ(d, p, 2, a_idx);
        let two_b = div_succ(d, p, 2, b_idx);
        let target_ab = radd(d, two_a, two_b);

        let raw = one_sided_bound(d, p, x, a_idx, b_idx);
        // raw : diff_ab <= raw_bound(a_idx,b_idx) = Y+(X+Y), X:=1/(a_idx+1), Y:=1/(b_idx+1)
        let one_a_plus_one_b = radd(d, one_a, one_b);
        let raw_bound = radd(d, one_b, one_a_plus_one_b);
        let raw_le_double = raw_bound_le_double(d, p, a_idx, b_idx);
        // raw_le_double : raw_bound <= (X+X)+(Y+Y)
        let aa = radd(d, one_a, one_a);
        let bb = radd(d, one_b, one_b);
        let raw_target = radd(d, aa, bb);

        // (X+X)+(Y+Y) = natDivSucc(2,a_idx)+natDivSucc(2,b_idx), via
        // `double_div_succ_eq` on each summand.
        let double_a = double_div_succ_eq(d, p, a_idx);
        let double_b = double_div_succ_eq(d, p, b_idx);
        let step_a = rcongr(d, aa, two_a, double_a, &|d, t| radd(d, t, bb));
        let mid = radd(d, two_a, bb);
        let step_b = rcongr(d, bb, two_b, double_b, &|d, t| radd(d, two_a, t));
        let (_, raw_target_eq_target) =
            rchain(d, raw_target, &[(mid, step_a), (target_ab, step_b)]);
        // raw_target_eq_target : Eq Rat raw_target target_ab

        // raw_target <= target_ab, via `le_refl` rewritten along the equality.
        let refl_target_ab = d.lemma(rat.le_refl, &[target_ab]);
        let eq_rev = rsymm(d, raw_target, target_ab, raw_target_eq_target);
        let raw_target_le =
            rat_eq_rewrite(d, target_ab, raw_target, eq_rev, refl_target_ab, &|d, t| {
                rle(d, rat, t, target_ab)
            });
        // raw_target_le : raw_target <= target_ab

        let raw_bound_le_target_ab = d.lemma(
            rat.le_trans,
            &[
                raw_bound,
                raw_target,
                target_ab,
                raw_le_double,
                raw_target_le,
            ],
        );
        let final_bound = d.lemma(
            rat.le_trans,
            &[diff_ab, raw_bound, target_ab, raw, raw_bound_le_target_ab],
        );
        (final_bound, target_ab)
    };

    let proof_mn = {
        let (upper, upper_target) = widen_direction(d, m, n);
        // upper : diff <= upper_target ; upper_target IS target (a_idx=m,b_idx=n).
        let _ = upper_target;

        let (bound_nm, target_nm) = widen_direction(d, n, m);
        // bound_nm : diff_nm <= target_nm = natDivSucc(2,n)+natDivSucc(2,m)
        let diff_nm = rsub(d, rat, sqrt_approx_x_n, sqrt_approx_x_m);

        let comm_target = d.lemma(rat.add_comm, &[div2_n, div2_m]);
        // comm_target : Eq Rat target_nm target
        let bound_nm2 = rat_eq_rewrite(d, target_nm, target, comm_target, bound_nm, &|d, t| {
            rle(d, rat, diff_nm, t)
        });
        // bound_nm2 : diff_nm <= target

        let flipped = d.lemma(rat.neg_le_neg, &[diff_nm, target, bound_nm2]);
        // flipped : -target <= -diff_nm
        let neg_sub_eq = d.lemma(rat.neg_sub, &[sqrt_approx_x_n, sqrt_approx_x_m]);
        // neg_sub_eq : Eq Rat (neg diff_nm) diff
        let neg_diff_nm = rneg(d, diff_nm);
        let neg_target = rneg(d, target);
        let lower = rat_eq_rewrite(d, neg_diff_nm, diff, neg_sub_eq, flipped, &|d, t| {
            rle(d, rat, neg_target, t)
        });

        let lower_ty = rle(d, rat, neg_target, diff);
        let upper_ty = rle(d, rat, diff, target);
        and_intro(d, p, lower_ty, upper_ty, lower, upper)
    };

    let value = {
        let with_n = d.lam_fv(n_fv, nat_ty, proof_mn);
        d.lam_fv(m_fv, nat_ty, with_n)
    };
    let full_ty = {
        let over_n = d.pi_fv(n_fv, nat_ty, claim);
        let over_mn = d.pi_fv(m_fv, nat_ty, over_n);
        d.pi_fv(x_fv, carrier, over_mn)
    };
    let full_value = d.lam_fv(x_fv, carrier, value);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sqrt_approx_kregular,
        uparams: vec![],
        ty: full_ty,
        value: full_value,
    })
}

/// `CReal.sqrt : CReal → CReal`, via `CReal.mk` directly — the same recipe
/// `convergence.rs`'s `converges_of_cauchy` already uses (`CReal.mk (speedup
/// ...) (regular_of_kregular ...)`), so no `Exists.rec` elimination is
/// needed: `sqrt x := CReal.mk (speedup (sqrtApprox x) 1) (regular_of_kregular
/// (sqrtApprox x) 1 (sqrtApproxKRegular x))`.
///
/// **Total, no `0 ≤ x` hypothesis.** `sqrtApprox` clamps every sample to
/// `Rat.max _ 0` before taking a `Nat` square root, so the construction never
/// inspects `x`'s sign; `0 ≤ x` is what `sqrt`'s own LAWS need (relating
/// `sqrt x` back to `x`), not the definition.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_sqrt_ctor(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let one_nat = d.num(1);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let f = d.const_app(p.sqrt_approx, &[x]);
    let kreg = d.lemma(p.sqrt_approx_kregular, &[x]);
    let reg_proof = d.lemma(p.regular_of_kregular, &[f, one_nat, kreg]);
    let speedup_term = d.const_app(p.speedup, &[f, one_nat]);
    let value_body = d.const_app(p.mk, &[speedup_term, reg_proof]);

    let value = d.lam_fv(x_fv, carrier, value_body);
    let ty = d.arrow(carrier, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sqrt,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 45),
    })
}

// =============================================================================
// `CReal.sqrt_congr`, and the laws it unlocks.
//
// `sqrt`'s only obstruction (this module's own opening docs) was a
// same-index, same-real estimate — `sqrtApproxKRegular`. `sqrt_congr` needs a
// same-index, CROSS-real estimate instead: at a shared candidate index `k`,
// bound `sqrtApprox x k − sqrtApprox y k` using `Equiv x y` (a bound
// relating `x`/`y` at one shared deep index `j := (k+1)^2`) in place of a
// single real's own `regular` between two different deep indices. The two
// arguments are otherwise identical — same bracket, same
// `sum_sq_le_sq_sum`/`rat_sq_le` squeeze — which is why [`one_sided_bound`]
// is not reused directly but mirrored: reusing it would need `a_idx = b_idx`
// baked in, which collapses several of its terms (`one_a = one_b`) in ways
// that would make the shared code harder to read than duplicating the
// (shorter, single-index) argument.
// =============================================================================

/// The bracket half of [`one_sided_bound`]'s per-side setup, for a single
/// `real`/`k`, with the shared `dd`/`pos`/`j`/`j_pos` supplied by the caller
/// (both reals in a cross comparison sample the SAME deep index `j`, unlike
/// `one_sided_bound`'s two different indices).
///
/// Returns `(q, u, u_sq, u1, u1_sq, s, lower, upper)`:
/// `q := Rat.max (CReal.seq real j) 0`, `u := sqrtApprox real k`, `u1` the
/// next `natSqrt` candidate up (`s+1`, not `sqrtApprox` at another index),
/// `lower : Rat.le u_sq q`, `upper : Rat.lt q u1_sq` — the same
/// `sqrt_approx_sq_bracket`-to-collapsed-`normalize` bridge
/// [`one_sided_bound`]'s own doc names.
#[allow(clippy::too_many_arguments)]
fn sqrt_bracket_pieces(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    real: ExprId,
    k: ExprId,
    dd: ExprId,
    pos: ExprId,
    j: ExprId,
    j_pos: ExprId,
) -> (
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
) {
    let rat = p.rat;
    let bracket = d.lemma(p.sqrt_approx_sq_bracket, &[real, k]);

    let sample_j = sample(d, p, real, j);
    let zero_rat = rzero(d, rat);
    let q = d.const_app(rat.max, &[sample_j, zero_rat]);
    let num_q = num(d, q);
    let a = d.const_app(rat.int.nat_abs, &[num_q]);
    let b = den(d, q);
    let scaled = NatOps::mul(d, a, j);
    let kk = NatOps::div(d, scaled, b);
    let s = d.const_app(p.nat_sqrt, &[kk]);
    let s1 = d.succ(s);
    let s_int = d.of_nat(s);
    let s1_int = d.of_nat(s1);
    let u = normalize(d, s_int, dd, pos);
    let u_sq = rmul(d, u, u);
    let u1 = normalize(d, s1_int, dd, pos);
    let u1_sq = rmul(d, u1, u1);

    let ssz = d.imul(s_int, s_int);
    let rep_s = normalize(d, ssz, j, j_pos);
    let s1sq = d.imul(s1_int, s1_int);
    let rep_s1 = normalize(d, s1sq, j, j_pos);

    let lower_ty = rle(d, rat, rep_s, q);
    let upper_ty = rlt(d, rat, q, rep_s1);
    let lower_raw = d.and_left(lower_ty, upper_ty, bracket);
    let upper_raw = d.and_right(lower_ty, upper_ty, bracket);

    let mul_normalize = d.lemma(
        rat.normalize_mul_normalize,
        &[s_int, dd, pos, s_int, dd, pos],
    );
    let mul_normalize_rev = rsymm(d, u_sq, rep_s, mul_normalize);
    let lower = rat_eq_rewrite(d, rep_s, u_sq, mul_normalize_rev, lower_raw, &|d, t| {
        rle(d, rat, t, q)
    });

    let mul_normalize1 = d.lemma(
        rat.normalize_mul_normalize,
        &[s1_int, dd, pos, s1_int, dd, pos],
    );
    let mul_normalize1_rev = rsymm(d, u1_sq, rep_s1, mul_normalize1);
    let upper = rat_eq_rewrite(d, rep_s1, u1_sq, mul_normalize1_rev, upper_raw, &|d, t| {
        rlt(d, rat, q, t)
    });

    (q, u, u_sq, u1, u1_sq, s, lower, upper)
}

/// The shared per-direction squeeze behind both [`cross_one_sided_bound`]
/// (the `Equiv`-hypothesis case, `sqrt_congr`) and
/// [`cross_one_sided_bound_of_le`] (the `le`-hypothesis case,
/// `sqrt_le_sqrt`): given a proof `reg_upper : Rat.le (sample a_real j -
/// sample b_real j) dd2j` at the shared deep index `j := (k+1)^2` — however
/// the caller derived it — returns
///
/// `Rat.le (Rat.sub (sqrtApprox a k) (sqrtApprox b k))
///         (Rat.add (natDivSucc 1 k) (Rat.add (natDivSucc 1 k) (natDivSucc 1 k)))`
///
/// The two callers differ ONLY in how `reg_upper` is obtained: `Equiv a b`
/// needs `halves` to extract the upper side of a two-sided `Within`
/// estimate; `le a b := ∀ n, Rat.le (seq a n - seq b n) (2/(n+1))` already
/// has the exact shape at `n := j`, so `reg_upper` is a bare application
/// with nothing to extract. Everything downstream (the `sub_max_le` clamp
/// step, the `sum_sq_le_sq_sum` squeeze, `rat_sq_le`,
/// [`succ_over_index_eq`]) is identical either way.
#[allow(clippy::too_many_lines)]
#[allow(clippy::too_many_arguments)]
fn cross_one_sided_bound_core(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_real: ExprId,
    b_real: ExprId,
    k: ExprId,
    dd: ExprId,
    pos: ExprId,
    j: ExprId,
    j_pos: ExprId,
    dd2j: ExprId,
    reg_upper: ExprId,
) -> ExprId {
    let rat = p.rat;

    let (q_a, u_a, u_a_sq, _u_a1, _u_a1_sq, _s_a, lower_a, _upper_a) =
        sqrt_bracket_pieces(d, p, a_real, k, dd, pos, j, j_pos);
    let (q_b, u_b, _u_b_sq, u_b1, u_b1_sq, s_b, _lower_b, upper_b) =
        sqrt_bracket_pieces(d, p, b_real, k, dd, pos, j, j_pos);

    let one_nat_lit = d.num(1);
    let two_nat_lit = d.num(2);

    // --- delta := q_a - q_b <= natDivSucc 2 j, via `reg_upper` at `j`. ---
    let sample_aj = sample(d, p, a_real, j);
    let sample_bj = sample(d, p, b_real, j);
    // reg_upper : sample a_real j - sample b_real j <= dd2j

    let zero_rat = rzero(d, rat);
    let zero_sub_zero_le = {
        let zero_sub_zero = rsub(d, rat, zero_rat, zero_rat);
        let sub_self = d.lemma(rat.sub_self, &[zero_rat]);
        let dd2j_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two_nat_lit, j]);
        rat_eq_rewrite(
            d,
            zero_sub_zero,
            zero_rat,
            sub_self,
            dd2j_nonneg,
            &|d, t| rle(d, rat, t, dd2j),
        )
    };
    let sub_max = d.lemma(
        rat.sub_max_le,
        &[
            sample_aj,
            zero_rat,
            sample_bj,
            zero_rat,
            dd2j,
            reg_upper,
            zero_sub_zero_le,
        ],
    );
    // sub_max : Rat.le (Rat.sub q_a q_b) dd2j

    let q_a_le = d.lemma(rat.le_of_sub_le, &[q_a, q_b, dd2j, sub_max]);
    // q_a_le : q_a <= q_b + dd2j

    let qb_plus_ddj = radd(d, q_b, dd2j);
    let step5 = d.lemma(rat.le_trans, &[u_a_sq, q_a, qb_plus_ddj, lower_a, q_a_le]);
    // step5 : u_a_sq <= q_b + dd2j

    let upper_b_le = d.lemma(rat.le_of_lt, &[q_b, u_b1_sq, upper_b]);
    let refl_ddj = d.lemma(rat.le_refl, &[dd2j]);
    let step7 = d.lemma(
        rat.add_le_add,
        &[q_b, u_b1_sq, dd2j, dd2j, upper_b_le, refl_ddj],
    );
    // step7 : q_b+dd2j <= u_b1_sq+dd2j

    let ub1sq_plus_ddj = radd(d, u_b1_sq, dd2j);
    let step8 = d.lemma(
        rat.le_trans,
        &[u_a_sq, qb_plus_ddj, ub1sq_plus_ddj, step5, step7],
    );
    // step8 : u_a_sq <= u_b1_sq + dd2j

    // --- dd2j <= e*e, e := d1+d1, d1 := natDivSucc 1 k. ---
    let d1 = div_succ(d, p, 1, k);
    let e = radd(d, d1, d1);
    let ee = rmul(d, e, e);
    let d1_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat_lit, k]);

    let bound_k = div_succ_sq_bound(d, p, k);
    // bound_k : natDivSucc(1,j) <= d1*d1
    let d1j = div_succ(d, p, 1, j);
    let d1_sq = rmul(d, d1, d1);
    let sum_bounds = d.lemma(rat.add_le_add, &[d1j, d1_sq, d1j, d1_sq, bound_k, bound_k]);
    // sum_bounds : d1j+d1j <= (d1*d1)+(d1*d1)
    let eq_dd2j = double_div_succ_eq(d, p, j);
    // eq_dd2j : Eq(d1j+d1j, dd2j)
    let d1j_plus_d1j = radd(d, d1j, d1j);
    let d1sq_plus_d1sq = radd(d, d1_sq, d1_sq);
    let sum_bounds_rw = rat_eq_rewrite(d, d1j_plus_d1j, dd2j, eq_dd2j, sum_bounds, &|d, t| {
        rle(d, rat, t, d1sq_plus_d1sq)
    });
    // sum_bounds_rw : dd2j <= d1sq_plus_d1sq

    let sq_sum_le = sum_sq_le_sq_sum(d, p, d1, d1, d1_nonneg, d1_nonneg);
    // sq_sum_le : d1sq_plus_d1sq <= e*e
    let mod_le_esq = d.lemma(
        rat.le_trans,
        &[dd2j, d1sq_plus_d1sq, ee, sum_bounds_rw, sq_sum_le],
    );
    // mod_le_esq : dd2j <= e*e

    let refl_ub1sq = d.lemma(rat.le_refl, &[u_b1_sq]);
    let step10 = d.lemma(
        rat.add_le_add,
        &[u_b1_sq, u_b1_sq, dd2j, ee, refl_ub1sq, mod_le_esq],
    );
    // step10 : u_b1_sq+dd2j <= u_b1_sq+e*e

    let ub1sq_plus_ee = radd(d, u_b1_sq, ee);
    let step11 = d.lemma(
        rat.le_trans,
        &[u_a_sq, ub1sq_plus_ddj, ub1sq_plus_ee, step8, step10],
    );
    // step11 : u_a_sq <= u_b1_sq + e*e

    let s1_b = d.succ(s_b);
    let u_b1_nonneg = normalize_of_nat_nonneg(d, p, s1_b, dd, pos);
    let e_nonneg = d.lemma(rat.add_nonneg, &[d1, d1, d1_nonneg, d1_nonneg]);
    let step12 = sum_sq_le_sq_sum(d, p, u_b1, e, u_b1_nonneg, e_nonneg);
    // step12 : u_b1_sq + e*e <= (u_b1+e)*(u_b1+e)

    let ub1_plus_e = radd(d, u_b1, e);
    let ub1_plus_e_sq = rmul(d, ub1_plus_e, ub1_plus_e);
    let step13 = d.lemma(
        rat.le_trans,
        &[u_a_sq, ub1sq_plus_ee, ub1_plus_e_sq, step11, step12],
    );
    // step13 : u_a_sq <= (u_b1+e)*(u_b1+e)

    let target_nonneg = d.lemma(rat.add_nonneg, &[u_b1, e, u_b1_nonneg, e_nonneg]);
    let squeeze = d.lemma(p.rat_sq_le, &[u_a, ub1_plus_e, step13, target_nonneg]);
    // squeeze : u_a <= u_b1+e

    // --- u_b1 = u_b + natDivSucc 1 k, so u_a - u_b <= natDivSucc 1 k + e. ---
    let succ_eq = succ_over_index_eq(d, p, s_b, k);
    // succ_eq : Eq Rat u_b1 (u_b + natDivSucc 1 k)  (the second summand defeq `d1`)
    let u_b_plus_d1 = radd(d, u_b, d1);
    let target_rewritten = rat_eq_rewrite(d, u_b1, u_b_plus_d1, succ_eq, squeeze, &|d, t| {
        let bound = radd(d, t, e);
        rle(d, rat, u_a, bound)
    });
    // target_rewritten : u_a <= (u_b + d1) + e

    let assoc = d.lemma(rat.add_assoc, &[u_b, d1, e]);
    let u_b_plus_d1_plus_e = radd(d, u_b_plus_d1, e);
    let d1_plus_e = radd(d, d1, e);
    let u_b_plus_d1pluse = radd(d, u_b, d1_plus_e);
    let rebound = rat_eq_rewrite(
        d,
        u_b_plus_d1_plus_e,
        u_b_plus_d1pluse,
        assoc,
        target_rewritten,
        &|d, t| rle(d, rat, u_a, t),
    );
    // rebound : u_a <= u_b + (d1+e)

    d.lemma(rat.sub_le_of_le, &[u_a, u_b, d1_plus_e, rebound])
    // : u_a - u_b <= d1 + (d1+d1)
}

/// `Rat.le (Rat.sub (sqrtApprox a k) (sqrtApprox b k))
///         (Rat.add (natDivSucc 1 k) (Rat.add (natDivSucc 1 k) (natDivSucc 1 k)))`,
/// from `hab : Equiv a b`.
///
/// The cross-real analogue of [`one_sided_bound`]: `a`/`b` are sampled at the
/// SAME index `k`, and the "how far apart are the two clamped samples" step
/// — `one_sided_bound`'s own `x`-regularity-between-two-indices call — is
/// replaced by `hab` instantiated at the one shared deep index `j :=
/// (k+1)^2`, with `halves` extracting the upper side of the resulting
/// `Within`. Everything else is [`cross_one_sided_bound_core`].
fn cross_one_sided_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_real: ExprId,
    b_real: ExprId,
    hab: ExprId,
    k: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = p.rat.int.nat;

    let dd = d.succ(k);
    let pos = one_le_succ(d, k);
    let j = NatOps::mul(d, dd, dd);
    let j_pos = d.lemma(nat.one_le_mul, &[dd, dd, pos, pos]);

    let dd2j = div_succ(d, p, 2, j);
    let hab_at_j = d.apply(hab, &[j]);
    // hab_at_j : Within (sample a_real j - sample b_real j) dd2j
    let sample_aj = sample(d, p, a_real, j);
    let sample_bj = sample(d, p, b_real, j);
    let sample_diff = rsub(d, rat, sample_aj, sample_bj);
    let (_reg_lower, reg_upper) = halves(d, p, sample_diff, dd2j, hab_at_j);
    // reg_upper : sample a_real j - sample b_real j <= dd2j

    cross_one_sided_bound_core(d, p, a_real, b_real, k, dd, pos, j, j_pos, dd2j, reg_upper)
}

/// The `le`-hypothesis analogue of [`cross_one_sided_bound`], for
/// `sqrt_le_sqrt`: from `hle : le a b` (`:= ∀ n, Rat.le (seq a n − seq b n)
/// (2/(n+1))`), instantiating at the shared deep index `j` already IS
/// `reg_upper` — no `halves` extraction needed, since `le` is one-sided by
/// definition. Everything else is [`cross_one_sided_bound_core`], identical
/// to the `Equiv` case.
fn cross_one_sided_bound_of_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_real: ExprId,
    b_real: ExprId,
    hle: ExprId,
    k: ExprId,
) -> ExprId {
    let nat = p.rat.int.nat;

    let dd = d.succ(k);
    let pos = one_le_succ(d, k);
    let j = NatOps::mul(d, dd, dd);
    let j_pos = d.lemma(nat.one_le_mul, &[dd, dd, pos, pos]);

    let dd2j = div_succ(d, p, 2, j);
    let reg_upper = d.apply(hle, &[j]);
    // reg_upper : sample a_real j - sample b_real j <= dd2j

    cross_one_sided_bound_core(d, p, a_real, b_real, k, dd, pos, j, j_pos, dd2j, reg_upper)
}

/// `CReal.sqrt_congr : ∀ x y, Equiv x y → Equiv (sqrt x) (sqrt y)`.
///
/// At index `n`, `CReal.seq (sqrt x) n` reduces — through `CReal.mk`'s
/// projection, `speedup`'s definition, and `mul_index` — to `sqrtApprox x
/// (mul_index 1 n)` by pure computation, exactly the reduction this module's
/// own concrete regression test already exercises. So the goal at `n` is a
/// [`cross_one_sided_bound`] claim at the single shared index `m := mul_index
/// 1 n` (both directions, the second via `Equiv.symm`), widened from
/// `natDivSucc 1 m + natDivSucc 2 m` up to the declared `natDivSucc 2 n` via
/// [`index_le`] (`natDivSucc 1 m <= natDivSucc 1 n`, `m` being deeper than
/// `n`) and `Rat.natDivSucc_scale` (`natDivSucc 2 m = natDivSucc 1 n`
/// EXACTLY — Bishop's speed-up index paying for itself with no slack, same
/// as [`super::speedup::declare_regular_of_kregular`]'s own use of it).
///
/// **Total, no `0 ≤ x`/`0 ≤ y` hypothesis** — same reason `sqrt` itself needs
/// none: the argument never inspects either real's sign, only how close
/// their clamped samples are.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_sqrt_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one_nat_lit = d.num(1);
    let m = mul_index(d, one_nat_lit, n);

    let forward = cross_one_sided_bound(d, p, x, y, h, m);
    // forward : sqrtApprox x m - sqrtApprox y m <= d1 + (d1+d1)   [d1 := natDivSucc 1 m]

    let h_symm = d.lemma(p.equiv_symm, &[x, y, h]);
    let backward = cross_one_sided_bound(d, p, y, x, h_symm, m);
    // backward : sqrtApprox y m - sqrtApprox x m <= d1 + (d1+d1)

    let d1 = div_succ(d, p, 1, m);
    let e = radd(d, d1, d1);
    let raw_bound = radd(d, d1, e);

    let u_x = {
        let f = d.const_app(p.sqrt_approx, &[x]);
        d.apply(f, &[m])
    };
    let u_y = {
        let f = d.const_app(p.sqrt_approx, &[y]);
        d.apply(f, &[m])
    };
    let diff = rsub(d, rat, u_x, u_y);
    let diff_yx = rsub(d, rat, u_y, u_x);

    // lower : -raw_bound <= diff, via `neg_le_neg` on `backward` then
    // rewriting `neg diff_yx` to `diff` along `Rat.neg_sub`.
    let flipped = d.lemma(rat.neg_le_neg, &[diff_yx, raw_bound, backward]);
    // flipped : -raw_bound <= -diff_yx
    let neg_sub_eq = d.lemma(rat.neg_sub, &[u_y, u_x]);
    // neg_sub_eq : Eq (neg diff_yx) diff
    let neg_diff_yx = rneg(d, diff_yx);
    let neg_raw_bound = rneg(d, raw_bound);
    let lower = rat_eq_rewrite(d, neg_diff_yx, diff, neg_sub_eq, flipped, &|d, t| {
        rle(d, rat, neg_raw_bound, t)
    });

    let lower_ty = rle(d, rat, neg_raw_bound, diff);
    let upper_ty = rle(d, rat, diff, raw_bound);
    let within_raw = and_intro(d, p, lower_ty, upper_ty, lower, forward);
    // within_raw : Within diff raw_bound   [raw_bound = d1 + (d1+d1)]

    // --- widen raw_bound up to natDivSucc 2 n. ---
    let d1n = div_succ(d, p, 1, n);
    let dd2n = div_succ(d, p, 2, n);
    let dd2m = div_succ(d, p, 2, m);

    let eq_e_dd2m = double_div_succ_eq(d, p, m);
    // eq_e_dd2m : Eq(d1+d1, dd2m)   [e = d1+d1]
    let scale = d.lemma(rat.nat_div_succ_scale, &[one_nat_lit, n]);
    // scale : Eq(dd2m, d1n)  (LHS is `natDivSucc (succ 1) (mul_index 1 n)`, defeq dd2m)
    let (_, e_eq_d1n) = rchain(d, e, &[(dd2m, eq_e_dd2m), (d1n, scale)]);
    // e_eq_d1n : Eq(e, d1n)

    let raw_bound_rw = rat_eq_rewrite(d, e, d1n, e_eq_d1n, within_raw, &|d, t| {
        let b = radd(d, d1, t);
        within(d, p, diff, b)
    });
    // raw_bound_rw : Within diff (d1+d1n)

    let order = {
        let scaled_index_le = index_le(d, p, one_nat_lit, one_nat_lit, n);
        // scaled_index_le : Rat.le (natDivSucc 1 (mul_index 1 n)) (natDivSucc 1 n)
        //                 = Rat.le d1 d1n
        let refl_d1n = d.lemma(rat.le_refl, &[d1n]);
        let sum_le = d.lemma(
            rat.add_le_add,
            &[d1, d1n, d1n, d1n, scaled_index_le, refl_d1n],
        );
        // sum_le : d1+d1n <= d1n+d1n
        let eq_dd2n = double_div_succ_eq(d, p, n);
        // eq_dd2n : Eq(d1n+d1n, dd2n)
        let d1n_plus_d1n = radd(d, d1n, d1n);
        rat_eq_rewrite(d, d1n_plus_d1n, dd2n, eq_dd2n, sum_le, &|d, t| {
            let lhs = radd(d, d1, d1n);
            rle(d, rat, lhs, t)
        })
        // : d1+d1n <= dd2n
    };

    let d1_plus_d1n = radd(d, d1, d1n);
    let within_final = weaken(d, p, diff, d1_plus_d1n, dd2n, raw_bound_rw, order);
    // within_final : Within diff dd2n

    let hyp_ty = equiv(d, p, x, y);
    let value = {
        let over_n = d.lam_fv(n_fv, nat_ty, within_final);
        let with_h = d.lam_fv(h_fv, hyp_ty, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let sqrt_x = d.const_app(p.sqrt, &[x]);
        let sqrt_y = d.const_app(p.sqrt, &[y]);
        let conclusion = equiv(d, p, sqrt_x, sqrt_y);
        let inner = d.arrow(hyp_ty, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sqrt_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sqrt_le_sqrt : ∀ x y, le x y → le (sqrt x) (sqrt y)`.
///
/// **Total, no `0 ≤ x` hypothesis** — `le x y` alone suffices, for the same
/// reason `sqrt`/`sqrt_congr` need none: `sqrtApprox` clamps every sample to
/// `Rat.max _ 0` before comparing, and `Rat.sub_max_le` (used inside
/// [`cross_one_sided_bound_core`]) relates the two clamped samples from the
/// RAW samples' one-sided difference alone — it never needs to know either
/// raw sample's own sign, only that `q_a - q_b <= bound` follows from `a - b
/// <= bound` (with `bound >= 0`) regardless of whether `a` or `b` is
/// negative. This is exactly the fact that made `sqrt` itself total in the
/// first place, reused one level up.
///
/// The proof is the forward-only, `Rat.le`-only HALF of [`declare_sqrt_congr`]'s
/// argument: at index `n`, `CReal.seq (sqrt x) n`/`CReal.seq (sqrt y) n`
/// reduce to `sqrtApprox x m`/`sqrtApprox y m` (`m := mul_index 1 n`) exactly
/// as there, so the goal is a single [`cross_one_sided_bound_of_le`] claim at
/// `m`, widened from `natDivSucc 1 m + natDivSucc 2 m` up to the declared
/// `natDivSucc 2 n` via the identical `index_le`/`double_div_succ_eq`/
/// `nat_div_succ_scale` steps `declare_sqrt_congr` uses for its own forward
/// direction. No `Equiv.symm`/backward direction and no `And.intro`/
/// `neg_le_neg` combination step are needed, since `le`'s conclusion is
/// already one-sided.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_sqrt_le_sqrt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat_ty = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one_nat_lit = d.num(1);
    let m = mul_index(d, one_nat_lit, n);

    let forward = cross_one_sided_bound_of_le(d, p, x, y, h, m);
    // forward : sqrtApprox x m - sqrtApprox y m <= d1 + (d1+d1)   [d1 := natDivSucc 1 m]

    let d1 = div_succ(d, p, 1, m);
    let e = radd(d, d1, d1);

    let u_x = {
        let f = d.const_app(p.sqrt_approx, &[x]);
        d.apply(f, &[m])
    };
    let u_y = {
        let f = d.const_app(p.sqrt_approx, &[y]);
        d.apply(f, &[m])
    };
    let diff = rsub(d, rat, u_x, u_y);

    // --- widen `d1 + e` up to `natDivSucc 2 n`, identically to
    // `declare_sqrt_congr`'s forward-direction widening. ---
    let d1n = div_succ(d, p, 1, n);
    let dd2n = div_succ(d, p, 2, n);
    let dd2m = div_succ(d, p, 2, m);

    let eq_e_dd2m = double_div_succ_eq(d, p, m);
    // eq_e_dd2m : Eq(d1+d1, dd2m)   [e = d1+d1]
    let scale = d.lemma(rat.nat_div_succ_scale, &[one_nat_lit, n]);
    // scale : Eq(dd2m, d1n)
    let (_, e_eq_d1n) = rchain(d, e, &[(dd2m, eq_e_dd2m), (d1n, scale)]);
    // e_eq_d1n : Eq(e, d1n)

    let raw_bound_rw = rat_eq_rewrite(d, e, d1n, e_eq_d1n, forward, &|d, t| {
        let b = radd(d, d1, t);
        rle(d, rat, diff, b)
    });
    // raw_bound_rw : diff <= d1+d1n

    let order = {
        let scaled_index_le = index_le(d, p, one_nat_lit, one_nat_lit, n);
        // scaled_index_le : Rat.le (natDivSucc 1 (mul_index 1 n)) (natDivSucc 1 n)
        //                 = Rat.le d1 d1n
        let refl_d1n = d.lemma(rat.le_refl, &[d1n]);
        let sum_le = d.lemma(
            rat.add_le_add,
            &[d1, d1n, d1n, d1n, scaled_index_le, refl_d1n],
        );
        // sum_le : d1+d1n <= d1n+d1n
        let eq_dd2n = double_div_succ_eq(d, p, n);
        // eq_dd2n : Eq(d1n+d1n, dd2n)
        let d1n_plus_d1n = radd(d, d1n, d1n);
        rat_eq_rewrite(d, d1n_plus_d1n, dd2n, eq_dd2n, sum_le, &|d, t| {
            let lhs = radd(d, d1, d1n);
            rle(d, rat, lhs, t)
        })
        // : d1+d1n <= dd2n
    };

    let d1_plus_d1n = radd(d, d1, d1n);
    let within_final = d.lemma(
        rat.le_trans,
        &[diff, d1_plus_d1n, dd2n, raw_bound_rw, order],
    );
    // within_final : diff <= dd2n

    let hyp_ty = d.const_app(p.le, &[x, y]);
    let value = {
        let over_n = d.lam_fv(n_fv, nat_ty, within_final);
        let with_h = d.lam_fv(h_fv, hyp_ty, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let sqrt_x = d.const_app(p.sqrt, &[x]);
        let sqrt_y = d.const_app(p.sqrt, &[y]);
        let conclusion = d.const_app(p.le, &[sqrt_x, sqrt_y]);
        let inner = d.arrow(hyp_ty, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sqrt_le_sqrt,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sqrt_one : Equiv (sqrt one) one`.
///
/// The key simplification against the general `sqrtApproxKRegular`/
/// `sqrt_congr` machinery: `one := CReal.ofRat Rat.one` is a **constant**
/// sequence, so `CReal.seq one _` beta-reduces to `Rat.one` regardless of
/// its index argument's shape — even a symbolic one. That makes the clamped
/// sample `q := Rat.max (seq one j) Rat.zero` DEFEQ to `Rat.one` at every
/// index `j` (verified directly: a probe instantiating `j` with a free
/// variable and closing `Eq.refl q : Eq q Rat.one` via the kernel's own
/// defeq check succeeds, with a negative control confirming the checker can
/// fail). So [`CRealPrelude::sqrt_approx_sq_bracket`]'s two halves, applied
/// at `x := one`, are already stated (up to defeq) against the fixed value
/// `Rat.one` rather than against another sample of `x` — no cross-index
/// regularity step, no natSqrt uniqueness argument, and no rewrite of `q`
/// to `Rat.one` is even needed: passing a proof whose type mentions `q`
/// wherever a proof mentioning `Rat.one*Rat.one` is expected just
/// type-checks, because the kernel compares types up to defeq and `q` and
/// `Rat.one*Rat.one` share a normal form (also verified directly).
///
/// With that, `u := sqrtApprox one m` (`m` `sqrt`'s own `speedup` index at
/// `n`) satisfies `u*u <= Rat.one` and `Rat.one <= u1*u1` (`u1` the bracket's
/// "next candidate up") purely from the bracket's two halves, and
/// [`CRealPrelude::rat_sq_le`] turns each into `u <= 1` / `1 <= u1` with no
/// division. [`succ_over_index_eq`] relates `u1` back to `u + natDivSucc 1
/// m`, and from there `u - 1` is squeezed into `[-natDivSucc 1 m, natDivSucc
/// 1 m]` by ordinary `Rat` order lemmas — the same
/// `index_le`/`double_div_succ_eq` widening [`declare_sqrt_congr`] uses
/// brings that bound up to the declared `natDivSucc 2 n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_sqrt_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat_ty = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one_real = d.kernel().const_(p.one, vec![]);
    let one_nat_lit = d.num(1);
    let m = mul_index(d, one_nat_lit, n);

    // --- rebuild `sqrt_approx_sq_bracket`'s own pieces at (one, m). ---
    let dd = d.succ(m);
    let pos = one_le_succ(d, m);
    let j = NatOps::mul(d, dd, dd);
    let nat = p.rat.int.nat;
    let j_pos = d.lemma(nat.one_le_mul, &[dd, dd, pos, pos]);

    let sample_j = sample(d, p, one_real, j);
    let zero_rat = rzero(d, rat);
    let q = d.const_app(rat.max, &[sample_j, zero_rat]);

    let num_q = num(d, q);
    let a = d.const_app(rat.int.nat_abs, &[num_q]);
    let b = den(d, q);
    let scaled = NatOps::mul(d, a, j);
    let k = NatOps::div(d, scaled, b);
    let s = d.const_app(p.nat_sqrt, &[k]);
    let s1 = d.succ(s);

    let bracket = d.lemma(p.sqrt_approx_sq_bracket, &[one_real, m]);

    let s_int = d.of_nat(s);
    let s1_int = d.of_nat(s1);
    let ssz = d.imul(s_int, s_int);
    let rep_s = normalize(d, ssz, j, j_pos);
    let s1sq = d.imul(s1_int, s1_int);
    let rep_s1 = normalize(d, s1sq, j, j_pos);

    let lower_ty = rle(d, rat, rep_s, q);
    let upper_ty = rlt(d, rat, q, rep_s1);
    let lower_raw = d.and_left(lower_ty, upper_ty, bracket);
    let upper_raw = d.and_right(lower_ty, upper_ty, bracket);

    // u := sqrtApprox one m, defeq `normalize(s_int, dd, pos)`.
    let u = normalize(d, s_int, dd, pos);
    let u_sq = rmul(d, u, u);
    let mul_normalize_u = d.lemma(
        rat.normalize_mul_normalize,
        &[s_int, dd, pos, s_int, dd, pos],
    );
    // mul_normalize_u : Eq (u*u) rep_s
    let mul_normalize_u_rev = rsymm(d, u_sq, rep_s, mul_normalize_u);
    let lower = rat_eq_rewrite(d, rep_s, u_sq, mul_normalize_u_rev, lower_raw, &|d, t| {
        rle(d, rat, t, q)
    });
    // lower : u*u <= q

    let u1 = normalize(d, s1_int, dd, pos);
    let u1_sq = rmul(d, u1, u1);
    let mul_normalize_u1 = d.lemma(
        rat.normalize_mul_normalize,
        &[s1_int, dd, pos, s1_int, dd, pos],
    );
    // mul_normalize_u1 : Eq (u1*u1) rep_s1
    let mul_normalize_u1_rev = rsymm(d, u1_sq, rep_s1, mul_normalize_u1);
    let upper = rat_eq_rewrite(
        d,
        rep_s1,
        u1_sq,
        mul_normalize_u1_rev,
        upper_raw,
        &|d, t| rlt(d, rat, q, t),
    );
    // upper : q < u1*u1
    let upper_le = d.lemma(rat.le_of_lt, &[q, u1_sq, upper]);
    // upper_le : q <= u1*u1

    // --- q is defeq Rat.one*Rat.one (both reduce through the same constant
    // sample), so `lower`/`upper_le` type-check directly against
    // `ratSqLe`'s `s*s`-shaped hypothesis slot with `s := Rat.one`. ---
    let rone_val = rone(d, rat);
    let zero_lt_one = d.lemma(rat.zero_lt_one, &[]);
    let zero_le_rone = d.lemma(rat.le_of_lt, &[zero_rat, rone_val, zero_lt_one]);
    let u_le_rone = d.lemma(p.rat_sq_le, &[u, rone_val, lower, zero_le_rone]);
    // u_le_rone : Le u Rat.one

    let u1_nonneg = normalize_of_nat_nonneg(d, p, s1, dd, pos);
    let rone_le_u1 = d.lemma(p.rat_sq_le, &[rone_val, u1, upper_le, u1_nonneg]);
    // rone_le_u1 : Le Rat.one u1

    // --- u1 = u + natDivSucc 1 m, so bound `rone_le_u1` in terms of `u`. ---
    let succ_eq = succ_over_index_eq(d, p, s, m);
    // succ_eq : Eq u1 (u + natDivSucc 1 m)
    let d1 = div_succ(d, p, 1, m);
    let u_plus_d1 = radd(d, u, d1);
    let rone_le_u_plus_d1 = rat_eq_rewrite(d, u1, u_plus_d1, succ_eq, rone_le_u1, &|d, t| {
        rle(d, rat, rone_val, t)
    });
    // rone_le_u_plus_d1 : Le Rat.one (u + d1)

    let diff = rsub(d, rat, u, rone_val);

    // --- lower half: -d1 <= diff, from `rone <= u + d1` via `sub_le_of_le`
    //     at (rone, u, d1), giving `rone - u <= d1`, negated and rewritten
    //     along `neg_sub` -- the same two-step bridge `declare_sqrt_congr`
    //     uses for its own lower half.
    let rone_sub_u_le_d1 = d.lemma(rat.sub_le_of_le, &[rone_val, u, d1, rone_le_u_plus_d1]);
    // rone_sub_u_le_d1 : Le (rone - u) d1
    let rone_sub_u = rsub(d, rat, rone_val, u);
    let neg_le_neg_step = d.lemma(rat.neg_le_neg, &[rone_sub_u, d1, rone_sub_u_le_d1]);
    // neg_le_neg_step : Le (-d1) (-(rone-u))
    let neg_sub_eq = d.lemma(rat.neg_sub, &[rone_val, u]);
    // neg_sub_eq : Eq (neg (rone-u)) (u-rone) = diff
    let neg_d1 = rneg(d, d1);
    let neg_rone_sub_u = rneg(d, rone_sub_u);
    let lower_bound = rat_eq_rewrite(
        d,
        neg_rone_sub_u,
        diff,
        neg_sub_eq,
        neg_le_neg_step,
        &|d, t| rle(d, rat, neg_d1, t),
    );
    // lower_bound : Le (-d1) diff

    // --- upper half: diff <= d1, from `u <= rone` via `rat_le_add_nonneg`
    //     (rone <= rone + d1) and `sub_le_of_le`. ---
    let d1_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat_lit, m]);
    let rone_le_rone_plus_d1 = rat_le_add_nonneg(d, p, rone_val, d1, d1_nonneg);
    // rone_le_rone_plus_d1 : Le rone (rone+d1)
    let rone_plus_d1 = radd(d, rone_val, d1);
    let u_le_rone_plus_d1 = d.lemma(
        rat.le_trans,
        &[u, rone_val, rone_plus_d1, u_le_rone, rone_le_rone_plus_d1],
    );
    // u_le_rone_plus_d1 : Le u (rone+d1)
    let upper_bound = d.lemma(rat.sub_le_of_le, &[u, rone_val, d1, u_le_rone_plus_d1]);
    // upper_bound : Le diff d1   (diff = u - rone)

    let neg_d1_ty = rneg(d, d1);
    let lower_bound_ty = rle(d, rat, neg_d1_ty, diff);
    let upper_bound_ty = rle(d, rat, diff, d1);
    let within_raw = and_intro(
        d,
        p,
        lower_bound_ty,
        upper_bound_ty,
        lower_bound,
        upper_bound,
    );
    // within_raw : Within diff d1

    // --- widen d1 up to natDivSucc 2 n. ---
    let d1n = div_succ(d, p, 1, n);
    let dd2n = div_succ(d, p, 2, n);
    let scaled_index_le = index_le(d, p, one_nat_lit, one_nat_lit, n);
    // scaled_index_le : Le d1 d1n
    let d1n_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat_lit, n]);
    let d1n_le_double = rat_le_add_nonneg(d, p, d1n, d1n, d1n_nonneg);
    // d1n_le_double : Le d1n (d1n+d1n)
    let eq_dd2n = double_div_succ_eq(d, p, n);
    // eq_dd2n : Eq (d1n+d1n) dd2n
    let d1n_plus_d1n = radd(d, d1n, d1n);
    let d1n_le_dd2n = rat_eq_rewrite(d, d1n_plus_d1n, dd2n, eq_dd2n, d1n_le_double, &|d, t| {
        rle(d, rat, d1n, t)
    });
    // d1n_le_dd2n : Le d1n dd2n
    let d1_le_dd2n = d.lemma(rat.le_trans, &[d1, d1n, dd2n, scaled_index_le, d1n_le_dd2n]);
    // d1_le_dd2n : Le d1 dd2n

    let within_final = weaken(d, p, diff, d1, dd2n, within_raw, d1_le_dd2n);
    // within_final : Within diff dd2n

    let value = d.lam_fv(n_fv, nat_ty, within_final);
    let ty = {
        let sqrt_one_c = d.const_app(p.sqrt, &[one_real]);
        equiv(d, p, sqrt_one_c, one_real)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sqrt_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sqrt_zero : Equiv (sqrt zero) zero`.
///
/// The same constant-sample shortcut as [`declare_sqrt_one`], simpler still:
/// `CReal.seq CReal.zero _` beta-reduces to `Rat.zero` at every index, so the
/// bracket's clamped sample `q` is defeq `Rat.zero`, and both
/// [`CRealPrelude::rat_sq_le`] applications collapse `u := sqrtApprox zero m`
/// to EXACTLY `Rat.zero` (`u <= 0` from the lower half, `0 <= u` from
/// [`normalize_of_nat_nonneg`] directly — the SAME-index nonneg fact, not a
/// second bracket application), via `Rat.le_antisymm`. `diff := u - 0` is
/// then propositionally `0` outright (no widening chain needed at all: a
/// zero difference is `Within` any nonnegative bound immediately, the same
/// two-line argument [`declare_of_rat`]'s own regularity obligation uses).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sqrt_zero(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat_ty = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_nat_lit = d.num(1);
    let m = mul_index(d, one_nat_lit, n);

    // --- rebuild `sqrt_approx_sq_bracket`'s own pieces at (zero, m). ---
    let dd = d.succ(m);
    let pos = one_le_succ(d, m);
    let j = NatOps::mul(d, dd, dd);
    let nat = p.rat.int.nat;
    let j_pos = d.lemma(nat.one_le_mul, &[dd, dd, pos, pos]);

    let sample_j = sample(d, p, zero_real, j);
    let zero_rat = rzero(d, rat);
    let q = d.const_app(rat.max, &[sample_j, zero_rat]);

    let num_q = num(d, q);
    let a = d.const_app(rat.int.nat_abs, &[num_q]);
    let b = den(d, q);
    let scaled = NatOps::mul(d, a, j);
    let k = NatOps::div(d, scaled, b);
    let s = d.const_app(p.nat_sqrt, &[k]);
    let s1 = d.succ(s);

    let bracket = d.lemma(p.sqrt_approx_sq_bracket, &[zero_real, m]);

    let s_int = d.of_nat(s);
    let s1_int = d.of_nat(s1);
    let ssz = d.imul(s_int, s_int);
    let rep_s = normalize(d, ssz, j, j_pos);
    let s1sq = d.imul(s1_int, s1_int);
    let rep_s1 = normalize(d, s1sq, j, j_pos);

    let lower_ty = rle(d, rat, rep_s, q);
    let upper_ty = rlt(d, rat, q, rep_s1);
    let lower_raw = d.and_left(lower_ty, upper_ty, bracket);

    // u := sqrtApprox zero m, defeq `normalize(s_int, dd, pos)`.
    let u = normalize(d, s_int, dd, pos);
    let u_sq = rmul(d, u, u);
    let mul_normalize_u = d.lemma(
        rat.normalize_mul_normalize,
        &[s_int, dd, pos, s_int, dd, pos],
    );
    // mul_normalize_u : Eq (u*u) rep_s
    let mul_normalize_u_rev = rsymm(d, u_sq, rep_s, mul_normalize_u);
    let lower = rat_eq_rewrite(d, rep_s, u_sq, mul_normalize_u_rev, lower_raw, &|d, t| {
        rle(d, rat, t, q)
    });
    // lower : u*u <= q, q defeq Rat.zero*Rat.zero.

    let zero_le_zero = d.lemma(rat.le_refl, &[zero_rat]);
    let u_le_zero = d.lemma(p.rat_sq_le, &[u, zero_rat, lower, zero_le_zero]);
    // u_le_zero : Le u Rat.zero

    let u_nonneg = normalize_of_nat_nonneg(d, p, s, dd, pos);
    // u_nonneg : Le Rat.zero u

    let u_eq_zero = d.lemma(rat.le_antisymm, &[u, zero_rat, u_le_zero, u_nonneg]);
    // u_eq_zero : Eq u Rat.zero

    let diff = rsub(d, rat, u, zero_rat);
    let zero_minus_zero = rsub(d, rat, zero_rat, zero_rat);
    let congr_diff = rcongr(d, u, zero_rat, u_eq_zero, &|d, t| rsub(d, rat, t, zero_rat));
    // congr_diff : Eq diff zero_minus_zero
    let sub_self_zero = d.lemma(rat.sub_self, &[zero_rat]);
    // sub_self_zero : Eq zero_minus_zero Rat.zero
    let (_, diff_eq_zero) = rchain(
        d,
        diff,
        &[(zero_minus_zero, congr_diff), (zero_rat, sub_self_zero)],
    );
    // diff_eq_zero : Eq diff Rat.zero

    // --- Within Rat.zero dd2n, for the declared modulus, then transport
    //     along `diff_eq_zero` (reversed). ---
    let dd2n = div_succ(d, p, 2, n);
    let two_nat_lit = d.num(2);
    let dd2n_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two_nat_lit, n]);
    // dd2n_nonneg : Le Rat.zero dd2n
    let neg_dd2n_nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[dd2n, dd2n_nonneg]);
    // neg_dd2n_nonpos : Le (neg dd2n) Rat.zero
    let neg_dd2n_ty = rneg(d, dd2n);
    let lower_zero_ty = rle(d, rat, neg_dd2n_ty, zero_rat);
    let upper_zero_ty = rle(d, rat, zero_rat, dd2n);
    let within_zero = and_intro(
        d,
        p,
        lower_zero_ty,
        upper_zero_ty,
        neg_dd2n_nonpos,
        dd2n_nonneg,
    );
    // within_zero : Within Rat.zero dd2n

    let diff_eq_zero_rev = rsymm(d, diff, zero_rat, diff_eq_zero);
    let within_final = rat_eq_rewrite(d, zero_rat, diff, diff_eq_zero_rev, within_zero, &|d, t| {
        within(d, p, t, dd2n)
    });
    // within_final : Within diff dd2n

    let value = d.lam_fv(n_fv, nat_ty, within_final);
    let ty = {
        let sqrt_zero_c = d.const_app(p.sqrt, &[zero_real]);
        equiv(d, p, sqrt_zero_c, zero_real)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sqrt_zero,
        uparams: vec![],
        ty,
        value,
    })
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

    /// [`declare_sqrt_one`]'s whole route rests on `q := Rat.max (CReal.seq
    /// CReal.one j) Rat.zero`, and the `a`/`b` pieces `sqrtApprox`'s recipe
    /// derives from it, being DEFEQ to the concrete constants `Rat.one`/
    /// `Nat` `1` even when `j` is a SYMBOLIC free variable -- i.e. that
    /// `CReal.seq CReal.one _` beta-reduces to `Rat.one` regardless of its
    /// argument's shape, and that `Rat.max`, `Int.natAbs`, `Rat.num`,
    /// `Rat.den` then fully iota-reduce on the resulting CLOSED subterms
    /// even though the surrounding expression still mentions the free `j`.
    /// This pins that fact directly (with a negative control), independent
    /// of `declare_sqrt_one` itself compiling.
    #[test]
    fn one_bracket_pieces_are_defeq_to_concrete_one_even_at_symbolic_index() {
        use crate::rat_prelude::ops::{den, num, req, rone, rrefl, rzero};

        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let rat = p.rat;
        let nat_ty = d.nat_ty();
        let one_real = d.kernel().const_(p.one, vec![]);
        let anon = d.kernel().anon();

        // Build every fact as `∀ j : Nat, …`, so `j` is genuinely symbolic
        // rather than a dangling free variable `add_declaration` would
        // reject outright.
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let sample_j = sample(&mut d, p, one_real, j);
        let zero_rat = rzero(&mut d, rat);
        let q = d.const_app(rat.max, &[sample_j, zero_rat]);

        // q =?= Rat.one, via reflexivity across the defeq gap.
        let one_rat = rone(&mut d, rat);
        let q_ty_inner = req(&mut d, q, one_rat);
        let q_proof_inner = rrefl(&mut d, q);
        let q_ty = d.pi_fv(j_fv, nat_ty, q_ty_inner);
        let q_proof = d.lam_fv(j_fv, nat_ty, q_proof_inner);
        let name_q = d.kernel().name_str(anon, "__probe_q_eq_one");
        let result_q = d.kernel().add_declaration(Declaration::Theorem {
            name: name_q,
            uparams: vec![],
            ty: q_ty,
            value: q_proof,
        });
        assert!(
            result_q.is_ok(),
            "q must be defeq Rat.one even at a symbolic sample index: {:?}",
            result_q.err()
        );

        // Rebuild fresh (the previous `d.pi_fv`/`lam_fv` calls abstracted
        // `j_fv` out of scope) for the `a`/`b` checks.
        let j_fv2 = d.fresh_fvar();
        let j2 = d.kernel().fvar(j_fv2);
        let sample_j2 = sample(&mut d, p, one_real, j2);
        let q2 = d.const_app(rat.max, &[sample_j2, zero_rat]);
        let num_q = num(&mut d, q2);
        let a = d.const_app(rat.int.nat_abs, &[num_q]);
        let one_nat = d.num(1);
        let a_ty_inner = d.eq(a, one_nat);
        let a_proof_inner = d.refl(a);
        let a_ty = d.pi_fv(j_fv2, nat_ty, a_ty_inner);
        let a_proof = d.lam_fv(j_fv2, nat_ty, a_proof_inner);
        let name_a = d.kernel().name_str(anon, "__probe_a_eq_one");
        let result_a = d.kernel().add_declaration(Declaration::Theorem {
            name: name_a,
            uparams: vec![],
            ty: a_ty,
            value: a_proof,
        });
        assert!(
            result_a.is_ok(),
            "natAbs(num(q)) must be defeq Nat 1: {:?}",
            result_a.err()
        );

        // b := den(q) =?= Nat 1.
        let j_fv3 = d.fresh_fvar();
        let j3 = d.kernel().fvar(j_fv3);
        let sample_j3 = sample(&mut d, p, one_real, j3);
        let q3 = d.const_app(rat.max, &[sample_j3, zero_rat]);
        let b = den(&mut d, q3);
        let b_ty_inner = d.eq(b, one_nat);
        let b_proof_inner = d.refl(b);
        let b_ty = d.pi_fv(j_fv3, nat_ty, b_ty_inner);
        let b_proof = d.lam_fv(j_fv3, nat_ty, b_proof_inner);
        let name_b = d.kernel().name_str(anon, "__probe_b_eq_one");
        let result_b = d.kernel().add_declaration(Declaration::Theorem {
            name: name_b,
            uparams: vec![],
            ty: b_ty,
            value: b_proof,
        });
        assert!(
            result_b.is_ok(),
            "den(q) must be defeq Nat 1: {:?}",
            result_b.err()
        );

        // Negative control: a must NOT be defeq to Nat 2 -- otherwise this
        // probe could not distinguish a genuine reduction from a checker
        // that accepts anything.
        let j_fv4 = d.fresh_fvar();
        let j4 = d.kernel().fvar(j_fv4);
        let sample_j4 = sample(&mut d, p, one_real, j4);
        let q4 = d.const_app(rat.max, &[sample_j4, zero_rat]);
        let num_q4 = num(&mut d, q4);
        let a4 = d.const_app(rat.int.nat_abs, &[num_q4]);
        let two_nat = d.num(2);
        let a_ty_wrong_inner = d.eq(a4, two_nat);
        let a_proof_wrong_inner = d.refl(a4);
        let a_ty_wrong = d.pi_fv(j_fv4, nat_ty, a_ty_wrong_inner);
        let a_proof_wrong = d.lam_fv(j_fv4, nat_ty, a_proof_wrong_inner);
        let name_a_wrong = d.kernel().name_str(anon, "__probe_a_eq_two_must_fail");
        let result_a_wrong = d.kernel().add_declaration(Declaration::Theorem {
            name: name_a_wrong,
            uparams: vec![],
            ty: a_ty_wrong,
            value: a_proof_wrong,
        });
        assert!(
            result_a_wrong.is_err(),
            "natAbs(num(q)) must NOT be defeq Nat 2"
        );
    }

    /// [`declare_sqrt_one`] passes proofs whose type mentions the bracket's
    /// `q` directly into `ratSqLe`'s `s*s`-shaped hypothesis slot with
    /// `s := Rat.one`, relying on `q` and `Rat.one*Rat.one` sharing a normal
    /// form. Pins that defeq fact directly, independent of
    /// `declare_sqrt_one` itself compiling.
    #[test]
    fn rone_times_rone_is_defeq_rone() {
        use crate::rat_prelude::ops::{req, rmul, rone, rrefl};

        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let rat = p.rat;

        let one_rat = rone(&mut d, rat);
        let one_one = rmul(&mut d, one_rat, one_rat);
        let ty = req(&mut d, one_one, one_rat);
        let proof = rrefl(&mut d, one_one);
        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "__probe_rone_times_rone");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value: proof,
        });
        assert!(
            result.is_ok(),
            "Rat.one*Rat.one must be defeq Rat.one: {:?}",
            result.err()
        );
    }
}
