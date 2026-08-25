//! **`CReal.HasDerivativeOn`** (ADR-0512, continuing phase R11): the first
//! derivative in this kernel. Bishop's *uniform* differentiability on a
//! closed interval, built to the exact one-constructor-inductive shape
//! [`super::uniform_continuity::declare_uniform_continuity`]'s own module
//! documentation already justifies at length for `UniformlyContinuousOn` one
//! level down — `modulus : Nat -> Nat` is DATA for the identical reason
//! (`0 < x` and its `Nat` witness are the same proposition, yet the witness
//! cannot be pulled out of an `Exists` and used to build anything in `Type`),
//! so `HasDerivativeOn` is again declared in `Type`, with four leading
//! parameters `F F' a b` rather than `UniformlyContinuousOn`'s three, since
//! the derivative function `F'` is now itself part of the family.
//!
//! The four range hypotheses (`le a x`, `le x b`, `le a y`, `le y b`) are
//! reused **verbatim** from `UniformlyContinuousOn`'s own spec rather than a
//! bundled interval predicate — there is none in this file, and
//! `uniform_continuity.rs`'s own module documentation already explains why
//! not (the real-valued, index-free reading of a bound, not the
//! `Converges`/`Cauchy` canonical-sample idiom). `HasDerivativeOn`'s spec
//! bound is likewise real-valued and not `CReal.Within` (that predicate
//! bounds a *rational*, `Within r q := -q <= r /\ r <= q` for `r q : Rat`;
//! the derivative's error term and its bound are both `CReal`), so this file
//! builds its own two-argument closeness predicate the same way
//! `uniform_continuity.rs`'s private `close_within` does, generalised to an
//! arbitrary `CReal` bound rather than a literal `ofRat q` (`(1/(e+1)) * |y -
//! x|` is a product, not a rational constant).
//!
//! ## What this slice lands, and what it does not
//!
//! Landed: the carrier (`HasDerivativeOn`, its two projections `modulus` and
//! `spec`), two witnesses that show the predicate is not vacuous
//! (`hasDerivative_const`, `hasDerivative_id`, error term **exactly**
//! `Equiv`-zero regardless of the hypothesis, mirroring
//! `uniform_continuity.rs`'s own `id`/`const` witnesses, trivial modulus `fun
//! _ => 0`), and — added in a later pass — the first **nonlinear** witness,
//! `hasDerivative_sq : HasDerivativeOn (fun r => r*r) (fun x => x+x) a b`.
//! `sq`'s error term is `Equiv`-**exactly** `(y-x)*(y-x)`, not zero, so it
//! needed a from-scratch ring-algebra toolkit
//! (`neg_unique`/`mul_neg_equiv`/`neg_add_distrib`/`diff_of_squares`/
//! `sq_le_abs_sq`, below) that did not exist anywhere in [`CRealPrelude`]:
//! `diff_of_squares` gets the exact error identity (`y*y - x*x - (x+x)(y-x) =
//! (y-x)(y-x)`), and `sq_le_abs_sq` (`t*t <= |t|*|t|`, via `(|t|-t)(|t|+t) >=
//! 0` — one nonneg-product identity, no sign case-split, since `CReal.le` is
//! undecidable) gets the bound. Modulus is the identity, matching `id`'s.
//!
//! **Landed in a later pass still: `hasDerivative_neg` and `hasDerivative_add`
//! (the sum rule).** `hasDerivative_add` WAS blocked (below) and is unblocked
//! by [`RatPrelude::nat_div_succ_antitone`]; `hasDerivative_neg` was simply
//! not attempted before and turns out to need no new blocking lemma at all.
//! **Landed in a later pass still, once `abs_mul_le_of_bounds` closed:
//! `hasDerivative_smul` and `hasDerivative_sub`** (see below for the route).
//! **Not landed: the product rule** — see below for why.
//!
//! **`hasDerivative_neg` needed no new blocker at all.** `neg`'s scaling
//! factor is exactly `-1`, so `neg`'s error term at accuracy `e` is
//! **exactly** `neg` of `F`'s own error term at the SAME `e` — no rescaled
//! modulus, hence no antitonicity, hence no product-of-bounds lemma. The only
//! new fact needed is structural (`|-x| = |x|`, [`le_abs_neg_of_le_abs`]
//! below), plus the mirror-image multiplication law [`neg_mul_equiv_left`].
//!
//! **The sum rule (`hasDerivative_add`) WAS blocked on a missing rational
//! lemma, and the module documentation below is kept as it was written while
//! blocked** (the reasoning that follows is what a later pass, holding
//! [`RatPrelude::nat_div_succ_antitone`], used to unblock it — see
//! [`declare_has_derivative_add`]'s own doc comment for the closing
//! argument). Given `HasDerivativeOn F F' a b`
//! with modulus `mF` and `HasDerivativeOn G G' a b` with modulus `mG`, a
//! witness for `F + G` needs ONE combined modulus `mSum` such that, from a
//! single hypothesis `Within (y-x) (natDivSucc 1 (mSum e))`, BOTH `F`'s and
//! `G`'s own hypotheses become available. Whatever `mSum` is (`max (mF e) (mG
//! e)`, `mF e + mG e`, or any other combination that dominates both), this
//! step needs: from `Nat.le j j'`, derive `Rat.le (natDivSucc 1 j')
//! (natDivSucc 1 j)` — **`Rat.natDivSucc` antitone in its index, for two
//! arbitrary indices.** This lemma did not exist anywhere in this
//! development at the time this paragraph was written. `rat_prelude.rs`'s own
//! field documentation says so
//! explicitly, twice, independently: the comment on
//! [`RatPrelude::nat_div_succ_scale`] states outright that keeping
//! `natDivSucc` "antitone in its index... off the critical path" is the
//! reason that lemma is shaped the way it is, and
//! [`RatPrelude::nat_div_succ_le_one`] and [`RatPrelude::nat_div_succ_le_scaled`]
//! both carry a line reading "still **not** antitonicity of `natDivSucc` in
//! its index" about lemmas that look close. `uniform_continuity.rs`'s own
//! module documentation hits the identical wall for the identical reason
//! (closing `uniformly_continuous_imp_continuous_at` needs "a `Nat` `k`... with
//! `K/(n+1) <= 1/(modulus k + 1)`... a genuine `Nat`-division search", and
//! reports it as not built — that bridge is still not built).
//!
//! Checked before giving up on it (before it was unblocked):
//! [`RatPrelude::inv_le_of_pos_le`] (the
//! reciprocal is antitone on the positives) is close, but bridging it to two
//! `natDivSucc` VALUES needs `natDivSucc 1 j = inv (ofNat (j+1))` as an
//! equation, an `inv_inv` law for positive rationals, and a `Nat -> Rat`
//! embedding monotonicity fact — none of which this prelude exposes either,
//! and assembling all three from scratch is a rational-field development in
//! its own right, not a derivative-slice task, and would live in
//! `rat_prelude/` — out of scope for this lane (another lane holds it).
//! [`RatPrelude::nat_div_succ_le_scaled`] looked like a shortcut (it DOES
//! compare two different indices) but only for one SPECIFIC shape, `(c+1)*n +
//! c` against `n`, which is exactly what makes the scalar-multiple rule
//! below tractable and the sum rule not (by itself — `nat_div_succ_antitone`
//! is what actually closed it): combining two INDEPENDENT, ARBITRARY
//! moduli `mF`, `mG` has no such shared shape to exploit, and the fix used
//! `Nat.add` (`mF (2e+1) + mG (2e+1)`) plus antitonicity rather than any
//! shared-shape trick — see [`declare_has_derivative_add`].
//!
//! **The scalar-multiple rule (`hasDerivative_smul`) does NOT hit the
//! antitonicity wall, but it hits a DIFFERENT one, found while verifying the
//! route before building it.** The modulus rescaling is exactly as
//! previously scouted and IS correct: given a `Nat` bound `k` with `le (abs
//! c) (ofRat (natDivSucc (Nat.succ k) 0))` (`|c| <= k+1`), reading `F`'s own
//! spec at accuracy `e' := (k+1)*e + k` (rather than a fresh, incomparable
//! modulus) makes `(k+1) * natDivSucc 1 e' = natDivSucc 1 e` an EQUALITY —
//! [`RatPrelude::nat_div_succ_mul`] folds `(k+1) * natDivSucc 1 e'` to
//! `natDivSucc (k+1) e'`, and [`RatPrelude::nat_div_succ_scale`] at `c :=
//! k, m := e` reads `natDivSucc (k+1) ((k+1)*e+k)` as exactly `natDivSucc 1
//! e`. No antitonicity anywhere in that chain.
//!
//! What the rescaling does not supply is a bound on the resulting error term.
//! `smul`'s error is EXACTLY `c * error_F` where `error_F` is `F`'s own error
//! at `e'` — and closing the spec needs `abs (mul c error_F) <= (k+1) *
//! bound_F` from `abs c <= k+1` and `abs error_F <= bound_F`, i.e. a genuine
//! **two-variable** "product of two independently-bounded quantities is
//! bounded" lemma (`|c*t| <= A*B` from `|c|<=A`, `|t|<=B`, never deciding
//! either sign, since `CReal.le` is undecidable). This is a DIFFERENT, and
//! strictly harder, fact than `sq_le_abs_sq` below (which bounds `t*t`
//! against `|t|*|t|` for the SAME `t` via ONE nonneg-product identity,
//! `(|t|-t)(|t|+t) >= 0`). The two-variable version is still provable
//! case-split-free — `2*(A*B - c*t) = (A-c)(B+t) + (A+c)(B-t) >= 0` and
//! `2*(A*B + c*t) = (A+c)(B+t) + (A-c)(B-t) >= 0`, each a SUM of two
//! nonneg products — but that is TWO difference-of-squares-shaped expansions
//! per direction, roughly double `sq`'s algebra. **Landed in a later pass
//! still, once `abs_mul_le_of_bounds` closed: `hasDerivative_smul`** (route
//! exactly as scouted above — no antitonicity, the rescaled hypothesis at `e`
//! is *definitionally* `F`'s own hypothesis at `e'`) **and `hasDerivative_sub`**
//! (cheap composition of `hasDerivative_neg` and `hasDerivative_add`, no new
//! algebra). Both accepted by `Kernel::add_declaration` and axiom-free.
//!
//! **The product rule (`hasDerivative_mul`) is STILL not landed, and the
//! decomposition this file previously carried above was WRONG about which
//! function needs continuity — corrected here, numerically verified
//! (20+ random-rational trials, exact `Fraction` arithmetic, zero residual)
//! rather than re-derived by hand a second time:**
//!
//! ```text
//! F(y)G(y) − F(x)G(x) − (F'(x)G(x) + F(x)G'(x))(y−x)
//!   = F(y)·[G(y) − G(x) − G'(x)(y−x)]
//!   + G(x)·[F(y) − F(x) − F'(x)(y−x)]
//!   + (F(y) − F(x))·G'(x)·(y−x)
//! ```
//!
//! This needs `F(y)` bounded (for term 1), `G(x)` bounded (for term 2), and
//! **`F`'s own continuity** (for term 3, via `|F(y)-F(x)|`, `UniformlyContinuousOn`
//! is exactly the tool) plus `G'(x)` bounded (also term 3) — matching the
//! "boundedness of `F`, `G`, `F'`, `G'` plus continuity of `F`" this module
//! documentation always claimed, but the FORMULA it carried put the
//! continuity requirement on `G` instead (`(G(y)-G(x))·F'(x)·(y−x)` as the
//! third term, with `G(y)`/`F(x)` bounded) — algebraically correct as its own
//! identity (also numerically verified), just mislabeled against its own
//! prose. Swapping `F` and `G` throughout is what produces the formula above.
//!
//! Two things beyond `abs_mul_le_of_bounds` are still needed to build it, and
//! neither is a quick follow-on to `smul`:
//!
//! 1. **A genuinely three-way accuracy budget, unequally weighted.**
//!    `hasDerivative_add`'s `nat_div_succ_halve` fuses exactly TWO EQUAL
//!    contributions (`1/(2e+2) + 1/(2e+2) = 1/(e+1)`). Here three terms, each
//!    individually rescaled by a DIFFERENT `Nat` bound (`Bf`, `Bg`, `Bgp`,
//!    analogous to `smul`'s `k+1`), have to fuse to the same single
//!    `1/(e+1)` target — `smul`'s `nat_div_succ_scale` handles rescaling ONE
//!    term by one constant, and `_halve` handles splitting evenly in two;
//!    nothing in [`RatPrelude`] currently splits unevenly into three, and
//!    getting there without `Nat.sub` in an index (banned, see `CLAUDE.md`)
//!    is its own small lemma.
//! 2. **`UniformlyContinuousOn`'s own modulus/spec accessors are not
//!    imported into this file at all.** Its bound has a genuinely different
//!    SHAPE from a `HasDerivativeOn` error term: `|F(y)-F(x)| <= 1/(e3+1)`
//!    given `|y-x|` within a continuity modulus, with NO `|y-x|` factor on
//!    the right — term 3's `(F(y)-F(x))·G'(x)·(y−x)` bound comes from
//!    chaining that against `|G'(x)·(y−x)| <= Bgp·|y-x|` (itself a trivial
//!    `abs_mul_le_of_bounds` instance against `abs_le_self`), not from a
//!    single `hd_spec` call the way terms 1 and 2 do.
//!
//! Sized similarly to (or larger than) the sum rule, not a small addition to
//! `smul`.
//!
//! **The equal three-way accuracy split needs no new `rat_prelude` lemma —
//! it falls straight out of `Rat.natDivSucc_scale` one step past
//! `natDivSucc_halve`.** `natDivSucc_halve` is `natDivSucc_scale`'s `c := 1`
//! instance; the equal three-way split is the SAME identity at `c := 2`:
//!
//! ```text
//! natDivSucc 1 (3e+2) + natDivSucc 1 (3e+2) + natDivSucc 1 (3e+2)
//!   = natDivSucc 3 (3e+2)          -- natDivSucc_add, applied twice
//!   = natDivSucc 1 e               -- natDivSucc_scale, c := 2, m := e
//! ```
//!
//! `rescale_index(k, m) := (k+1)*m + k` is `natDivSucc_scale`'s own index
//! shape, reused at `k := 2` to build `3e+2` from `e` AND again at `k :=
//! k1/k2/k3` to rescale each of the product rule's three terms against its
//! own magnitude bound (`fold_index0_first`/`fold_index0_second`,
//! `smul`'s single rescale generalised to three independent bounds). This
//! is the reusable part of this slice regardless of whether the product
//! rule itself lands — it generalises past products of two functions to
//! any fixed-arity equal split, and needs nothing this prelude does not
//! already have.
//!
//! **`hasDerivative_mul` itself: built, `cargo check`/`clippy` clean, and
//! now KERNEL-VERIFIED.** A first `Kernel::add_declaration` attempt was
//! rejected in ~29s (an ordinary type error, not a large-term mismatch) on
//! an argument-order bug: four `esymm` calls in the "combine the three
//! terms" section (the ones lifting a raw `Rat`-level `add_assoc` to its
//! reverse direction) had their explicit `(a, b)` arguments swapped relative
//! to the underlying proof's own type, so `esymm` built `Equiv b a` from a
//! hypothesis actually typed `Equiv a b` read backwards — caught and fixed
//! by re-deriving each `add_assoc` call's real type by hand and checking it
//! against the adjacent comment, not by re-running the kernel. **Re-verified
//! since**: `cargo test -p axeyum-lean-kernel --lib creal::creal_tests::`
//! passes all 28 tests, including `creal_prelude_builds` (the whole prelude,
//! `hasDerivative_mul` included, kernel-checks with no `Err`) and
//! `every_creal_declaration_is_checked_and_axiom_free`.
//!
//! **Landed in a later pass still: `hasDerivative_cube`, with zero new
//! algebra.** `r*(r*r)` is exactly `id(r) * sq(r)`, so it is
//! [`declare_has_derivative_mul`]'s own theorem applied directly to
//! [`CRealPrelude::has_derivative_id`] and [`CRealPrelude::has_derivative_sq`],
//! with [`CRealPrelude::uniformly_continuous_id`] supplying the continuity
//! hypothesis the product rule's third term needs. The three magnitude
//! bounds (on `id`, on `sq`, and on `sq`'s own derivative `fun x=>x+x`) are
//! kept as three INDEPENDENT caller-supplied hypotheses rather than folded
//! into one via a single interval bound — folding them would need a rational
//! identity of the shape `natDivSucc(m,0) * natDivSucc(n,0) =
//! natDivSucc(m*n,0)`, which is not established anywhere in this prelude,
//! and is exactly the kind of gap that cost the sum rule its own
//! antitonicity blocker above. See [`CRealPrelude::has_derivative_cube`] for
//! the statement in full; kernel-verified (axiom-footprint 0) by the same
//! test run as `hasDerivative_mul`.
//!
//! **What this means for the next domino (general `hasDerivative_pow`,
//! `hasDerivative_chain`, or uniqueness of the derivative):** all three were
//! scouted and found to need genuinely new supporting infrastructure, not
//! present anywhere in this prelude, before any new algebra could even
//! start:
//!
//! - **`hasDerivative_pow` at general `n`, by induction from `hasDerivative_mul`**
//!   (rather than `hasDerivative_cube`'s direct `id * sq` composition) needs
//!   `UniformlyContinuousOn` and THREE independent `BoundedOn` facts about
//!   `F^(n-1)` at every inductive step — i.e. closure lemmas
//!   ("product of two bounded/continuous functions is bounded/continuous")
//!   that do not exist in `uniform_continuity.rs` or anywhere else in this
//!   file (checked: `uniform_continuity.rs` declares only the carrier, its
//!   projections, `uniformly_continuous_id`, and `uniformly_continuous_const`
//!   — no `_mul`, no `_add`). `hasDerivative_cube` sidesteps this entirely by
//!   composing `id` and `sq` directly instead of inducting.
//! - **`hasDerivative_chain`** needs (1) a hypothesis relating `F`'s range on
//!   `[a,b]` to `G`'s own domain (this file's convention of sharing one
//!   `[a,b]` across every function does not by itself make `F`'s image land
//!   in `[a,b]`, so either an explicit self-map hypothesis or a genuinely
//!   different domain `[c,e]` for `G` plus a range-mapping hypothesis is
//!   forced — a real, new hypothesis, not a simplification of one already
//!   here), and (2) composing `G`'s own accuracy target through `F`'s
//!   modulus via `UniformlyContinuousOn F a b`'s own continuity modulus
//!   (usable as-is, the same tool `hasDerivative_mul`'s third term already
//!   takes as an explicit hypothesis) — buildable in principle, but a
//!   genuinely new two-level modulus composition, not a reuse of the
//!   sum/product rescale machinery below.
//! - **Uniqueness of the derivative** (`HasDerivativeOn F F1 a b ->
//!   HasDerivativeOn F F2 a b -> Equiv (F1 x) (F2 x)` for `x` in `[a,b]`)
//!   needs a closing lemma of the shape "if `le (abs v) (ofRat (natDivSucc 1
//!   e))` for every `e : Nat`, then `Equiv v zero`" at the ABSTRACT `le`
//!   level. `CReal.equiv_of_bounded` is the nearest fact in this prelude and
//!   is NOT it: it operates on `seq x n` directly (`∀ n, Within (seq x n −
//!   seq y n) (natDivSucc K n)) → Equiv x y`), a lower-level API this file
//!   never touches, and bridging an abstract `∀ e, le (abs v) (...)` fact
//!   down to a `seq`-level bound is its own undertaking. Separately, proving
//!   `F1(x) ~ F2(x)` also needs a witness `y != x` inside `[a,b]` arbitrarily
//!   close to `x`, chosen WITHOUT deciding `x`'s position relative to `a`/`b`
//!   (`CReal.le` is undecidable) — a convex-combination construction
//!   sidesteps the branching (see the reasoning trace for this session), but
//!   still needs a "cancel by a known-positive scalar" lemma this file does
//!   not have either. None of this is a dead end, but none of it is cheap,
//!   and this session left it unbuilt rather than risk a partial, unverified
//!   attempt at either.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::ring_helpers::{add4_comm, right_distrib};
use super::{CRealPrelude, creal_ty};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite};

/// Admit `CReal.HasDerivativeOn` (the carrier and its two projections) and
/// two witnesses: `hasDerivative_const` and `hasDerivative_id`. See the
/// module documentation for why the sum rule, the scalar-multiple rule and
/// the product rule are not landed here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_derivative(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_carrier(d, p)?;
    declare_projections(d, p)?;
    declare_has_derivative_const(d, p)?;
    declare_has_derivative_id(d, p)?;
    declare_has_derivative_sq(d, p)?;
    declare_has_derivative_neg(d, p)?;
    declare_has_derivative_add(d, p)?;
    declare_abs_mul_le_of_bounds(d, p)?;
    declare_has_derivative_smul(d, p)?;
    declare_has_derivative_sub(d, p)?;
    declare_has_derivative_mul(d, p)?;
    declare_has_derivative_cube(d, p)?;
    declare_has_derivative_congr(d, p)
    // `hasDerivative_pow_two` is NOT called here: it mentions `CReal.pow`,
    // which `power.rs` declares later in `build_creal_prelude_uncached`'s own
    // pipeline. See `declare_has_derivative_pow_two`'s doc comment and the
    // call site in `creal.rs`.
}

// --- shared term builders ----------------------------------------------------

/// `CReal -> CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `Nat -> Nat`.
fn nat_fn_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `add x (neg y)` — `x - y`.
fn cdiff(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    cadd(d, p, x, ny)
}

/// `Rat.natDivSucc k j`, with a literal numerator `k`.
fn div_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    d.const_app(p.rat.nat_div_succ, &[numerator, j])
}

/// `Rat.natDivSucc numerator j`, with an arbitrary numerator EXPRESSION
/// (unlike [`div_succ`], which fixes it to a literal `u32`) — needed for
/// `hasDerivative_smul`'s scalar bound `k+1`, where `k` is a universally
/// quantified `Nat`, not a constant.
fn div_succ_expr(d: &mut IntDev<'_>, p: CRealPrelude, numerator: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[numerator, j])
}

/// `le (abs v) q` — `v` bounded by `q` in magnitude, both `CReal`. The
/// derivative's own two-argument closeness predicate, generalising
/// `uniform_continuity.rs`'s private `close_within` (which fixes the bound
/// to a literal `ofRat q`) to an arbitrary `CReal` bound — the error term's
/// bound here is a product, `(1/(e+1)) * |y-x|`, not a rational constant.
fn within_real(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId, q: ExprId) -> ExprId {
    let magnitude = cabs(d, p, v);
    d.const_app(p.le, &[magnitude, q])
}

/// `CReal.HasDerivativeOn F F' a b`.
fn hd_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.has_derivative_on, &[f, fp, a, b])
}

/// Chain `Equiv start ...` through `(next, step)` pairs — the `echain` idiom
/// used throughout this development (private to each module that needs it;
/// see `series.rs`'s own copy for why it is rebuilt here rather than
/// imported).
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

/// `Equiv (neg zero) zero` — the group identity `-0 = 0`, copied from
/// `series.rs::neg_zero_equiv` (private to its own module) rather than
/// imported.
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]); // padded ~ nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // nz ~ padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
    let h3 = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero_c
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// `(term, proof)` = `(ofRat (natDivSucc k idx), le zero term)` — the
/// rational bound `k/(idx+1)` lifted to `CReal`, and a proof it is
/// nonnegative, via `Rat.zero_le_natDivSucc` and `CReal.ofRat_le`.
fn nonneg_rat_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, idx: ExprId) -> (ExprId, ExprId) {
    let q = div_succ(d, p, k, idx);
    let ofr_q = d.const_app(p.of_rat, &[q]);
    let rzero_expr = crate::rat_prelude::ops::rzero(d, p.rat);
    let numerator = d.num(k);
    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[numerator, idx]);
    let proof = d.lemma(p.of_rat_le, &[rzero_expr, q, rat_nonneg]);
    (ofr_q, proof)
}

/// `(bound, proof)` = `(mul (ofRat (natDivSucc 1 e)) (abs diff), le zero
/// bound)` — the standard target error bound `(1/(e+1)) * |y-x|` from the
/// derivative's own spec, and a proof it is nonnegative
/// ([`CRealPrelude::mul_nonneg`] applied to [`nonneg_rat_bound`] and
/// [`CRealPrelude::abs_nonneg`]).
fn error_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e: ExprId,
    diff_yx: ExprId,
) -> (ExprId, ExprId) {
    let (ofr_e, ofr_e_nonneg) = nonneg_rat_bound(d, p, 1, e);
    let abs_diff = cabs(d, p, diff_yx);
    let abs_diff_nonneg = d.lemma(p.abs_nonneg, &[diff_yx]);
    let bound = cmul(d, p, ofr_e, abs_diff);
    let bound_nonneg = d.lemma(
        p.mul_nonneg,
        &[ofr_e, abs_diff, ofr_e_nonneg, abs_diff_nonneg],
    );
    (bound, bound_nonneg)
}

/// From `v_equiv_zero : Equiv v zero` and `zero_le_bound : le zero bound`,
/// derive `le (abs v) bound` — the common closing step for a derivative
/// witness whose error term is exactly zero (up to `Equiv`):
/// [`CRealPrelude::abs_le`] applied to `le v bound` (from `v ~ zero <=
/// bound`) and `le (neg v) bound` (from `neg v ~ neg zero ~ zero <= bound`).
fn close_zero_error(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    v_equiv_zero: ExprId,
    zero_le_bound: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);

    let v_le_zero = d.lemma(p.le_of_equiv, &[v, zero_c, v_equiv_zero]);
    let h_upper = d.lemma(p.le_trans, &[v, zero_c, bound, v_le_zero, zero_le_bound]);

    let nv = cneg(d, p, v);
    let neg_zero_c = cneg(d, p, zero_c);
    let nv_eq_negzero = d.lemma(p.neg_congr, &[v, zero_c, v_equiv_zero]); // nv ~ neg_zero_c
    let nz_eq = neg_zero_equiv(d, p); // neg_zero_c ~ zero_c
    let nv_equiv_zero = echain(d, p, nv, &[(neg_zero_c, nv_eq_negzero), (zero_c, nz_eq)]);
    let nv_le_zero = d.lemma(p.le_of_equiv, &[nv, zero_c, nv_equiv_zero]);
    let h_lower = d.lemma(p.le_trans, &[nv, zero_c, bound, nv_le_zero, zero_le_bound]);

    d.lemma(p.abs_le, &[v, bound, h_upper, h_lower])
}

/// `∀ (e : Nat) (x y : CReal), le a x → le x b → le a y → le y b →
///   le (abs (add y (neg x))) (ofRat (natDivSucc 1 (modulus e))) →
///   le (abs (add (add (F y) (neg (F x))) (neg (mul (F' x) (add y (neg
///   x)))))) (mul (ofRat (natDivSucc 1 e)) (abs (add y (neg x))))`.
fn deriv_spec_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    a: ExprId,
    b: ExprId,
    modulus: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let range_ax = d.const_app(p.le, &[a, x]);
    let range_xb = d.const_app(p.le, &[x, b]);
    let range_ay = d.const_app(p.le, &[a, y]);
    let range_yb = d.const_app(p.le, &[y, b]);

    let diff_yx = cdiff(d, p, y, x);

    let mod_e = d.apply(modulus, &[e]);
    let in_bound = div_succ(d, p, 1, mod_e);
    let ofr_in_bound = d.const_app(p.of_rat, &[in_bound]);
    let hyp = within_real(d, p, diff_yx, ofr_in_bound);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let fpx = d.apply(fp, &[x]);
    let deriv_term = cmul(d, p, fpx, diff_yx);
    let fy_fx = cdiff(d, p, fy, fx);
    let error = cdiff(d, p, fy_fx, deriv_term);

    let out_bound_rat = div_succ(d, p, 1, e);
    let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);
    let abs_diff = cabs(d, p, diff_yx);
    let out_bound = cmul(d, p, ofr_out, abs_diff);
    let conclusion = within_real(d, p, error, out_bound);

    let body = d.arrow(hyp, conclusion);
    let with_yb = d.arrow(range_yb, body);
    let with_ay = d.arrow(range_ay, with_yb);
    let with_xb = d.arrow(range_xb, with_ay);
    let with_ax = d.arrow(range_ax, with_xb);
    let with_y = d.pi_fv(y_fv, carrier, with_ax);
    let with_x = d.pi_fv(x_fv, carrier, with_y);
    d.pi_fv(e_fv, nat, with_x)
}

// --- ring algebra helpers (support the `sq` witness) -------------------------
//
// None of this is specific to squares. It is the "difference of squares"
// toolkit `uniform_continuity.rs`'s own module documentation flagged as
// missing for scalar multiplication (`mul a (neg y) ~ neg (mul a y)`, needed
// there and never built). `hasDerivative_sq`'s error-term identity AND its
// bound both need it, so it is built here, once, from the group/ring laws
// already in [`CRealPrelude`], and used twice.

/// `Equiv a a`.
fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// From `h : Equiv a b`, `Equiv b a`.
fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// `Equiv (add (neg x) x) zero` — `add_neg` with its two operands commuted.
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

/// From `h_ab_zero : Equiv (add a b) zero`, `Equiv b (neg a)` — `b` is the
/// unique additive inverse of `a`. Purely group-theoretic:
/// `b ~ 0+b ~ (-a+a)+b ~ -a+(a+b) ~ -a+0 ~ -a`.
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

/// `Equiv (neg (neg x)) x` — double negation, from [`neg_unique`] applied to
/// [`neg_add_self`].
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (mul x (neg y)) (neg (mul x y))`.
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

/// `Equiv (neg (add a b)) (add (neg a) (neg b))`.
fn neg_add_distrib(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let ab = cadd(d, p, a, b);
    let na_nb = cadd(d, p, na, nb);
    let b_na = cadd(d, p, b, na);
    let na_b = cadd(d, p, na, b);
    let b_nanb = cadd(d, p, b, na_nb);
    let b_na_nb = cadd(d, p, b_na, nb);
    let na_b_nb = cadd(d, p, na_b, nb);
    let b_nb = cadd(d, p, b, nb);
    let na_bnb = cadd(d, p, na, b_nb);
    let na_zero = cadd(d, p, na, zero_c);
    let ab_nanb = cadd(d, p, ab, na_nb);
    let a_bnanb = cadd(d, p, a, b_nanb);
    let a_na = cadd(d, p, a, na);
    let neg_ab = cneg(d, p, ab);

    let step2 = d.lemma(p.add_assoc, &[b, na, nb]);
    let step2_symm = esymm(d, p, b_na_nb, b_nanb, step2);

    let step3 = d.lemma(p.add_comm, &[b, na]);
    let refl_nb = erefl(d, p, nb);
    let step4 = d.lemma(p.add_congr, &[b_na, na_b, nb, nb, step3, refl_nb]);

    let step5 = d.lemma(p.add_assoc, &[na, b, nb]);

    let step6 = d.lemma(p.add_neg, &[b]);
    let refl_na = erefl(d, p, na);
    let step7 = d.lemma(p.add_congr, &[na, na, b_nb, zero_c, refl_na, step6]);

    let step8 = d.lemma(p.add_zero, &[na]);

    let middle_result = echain(
        d,
        p,
        b_nanb,
        &[
            (b_na_nb, step2_symm),
            (na_b_nb, step4),
            (na_bnb, step5),
            (na_zero, step7),
            (na, step8),
        ],
    );

    let refl_a = erefl(d, p, a);
    let step9 = d.lemma(p.add_congr, &[a, a, b_nanb, na, refl_a, middle_result]);
    let step10 = d.lemma(p.add_neg, &[a]);

    let step1 = d.lemma(p.add_assoc, &[a, b, na_nb]);

    let h = echain(
        d,
        p,
        ab_nanb,
        &[(a_bnanb, step1), (a_na, step9), (zero_c, step10)],
    );

    let nu = neg_unique(d, p, ab, na_nb, h);
    esymm(d, p, na_nb, neg_ab, nu)
}

/// `Equiv (add (add x (neg y)) (add y (neg z))) (add x (neg z))` — cancelling
/// a middle `+y −y` pair.
fn cancel_middle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, z: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let nz = cneg(d, p, z);
    let x_ny = cadd(d, p, x, ny);
    let y_nz = cadd(d, p, y, nz);
    let outer = cadd(d, p, x_ny, y_nz);
    let x_negz = cadd(d, p, x, nz);
    let ny_y = cadd(d, p, ny, y);
    let ny_y_nz = cadd(d, p, ny_y, nz);
    let ny_yz = cadd(d, p, ny, y_nz);
    let zero_nz = cadd(d, p, zero_c, nz);
    let nz_zero = cadd(d, p, nz, zero_c);
    let x_plus_nyyz = cadd(d, p, x, ny_yz);

    let inner_assoc = d.lemma(p.add_assoc, &[ny, y, nz]);
    let inner_assoc_symm = esymm(d, p, ny_y_nz, ny_yz, inner_assoc);

    let ny_y_zero = neg_add_self(d, p, y);
    let refl_nz = erefl(d, p, nz);
    let step_zero = d.lemma(p.add_congr, &[ny_y, zero_c, nz, nz, ny_y_zero, refl_nz]);

    let comm_znz = d.lemma(p.add_comm, &[zero_c, nz]);
    let step_trim = d.lemma(p.add_zero, &[nz]);
    let zero_nz_to_nz = echain(d, p, zero_nz, &[(nz_zero, comm_znz), (nz, step_trim)]);

    let middle_result = echain(
        d,
        p,
        ny_yz,
        &[
            (ny_y_nz, inner_assoc_symm),
            (zero_nz, step_zero),
            (nz, zero_nz_to_nz),
        ],
    );

    let refl_x = erefl(d, p, x);
    let step_final = d.lemma(p.add_congr, &[x, x, ny_yz, nz, refl_x, middle_result]);

    let outer_assoc = d.lemma(p.add_assoc, &[x, ny, y_nz]);

    echain(
        d,
        p,
        outer,
        &[(x_plus_nyyz, outer_assoc), (x_negz, step_final)],
    )
}

/// `Equiv (mul (add a (neg b)) (add a b)) (add (mul a a) (neg (mul b b)))` —
/// `(a-b)*(a+b) ~ a*a - b*b`.
fn diff_of_squares(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = cneg(d, p, b);
    let big_a = cadd(d, p, a, nb);
    let big_b = cadd(d, p, a, b);
    let lhs0 = cmul(d, p, big_a, big_b);
    let mul_a_a = cmul(d, p, a, a);
    let mul_a_b = cmul(d, p, a, b);
    let mul_b_a = cmul(d, p, b, a);
    let mul_b_b = cmul(d, p, b, b);
    let neg_mul_a_b = cneg(d, p, mul_a_b);
    let neg_mul_b_b = cneg(d, p, mul_b_b);
    let mul_a_nb = cmul(d, p, a, nb);
    let mul_b_nb = cmul(d, p, b, nb);
    let mul_biga_a = cmul(d, p, big_a, a);
    let mul_biga_b = cmul(d, p, big_a, b);
    let mul_a_biga = cmul(d, p, a, big_a);
    let mul_b_biga = cmul(d, p, b, big_a);
    let target1 = cadd(d, p, mul_biga_a, mul_biga_b);
    let big_p = cadd(d, p, mul_a_a, neg_mul_a_b);
    let big_q = cadd(d, p, mul_a_b, neg_mul_b_b);
    let pq = cadd(d, p, big_p, big_q);
    let final_rhs = cadd(d, p, mul_a_a, neg_mul_b_b);

    let step1 = d.lemma(p.left_distrib, &[big_a, a, b]);

    let c1 = d.lemma(p.mul_comm, &[big_a, a]);
    let c2 = d.lemma(p.left_distrib, &[a, a, nb]);
    let add_aa_anb = cadd(d, p, mul_a_a, mul_a_nb);
    let c3 = mul_neg_equiv(d, p, a, b);
    let refl_aa = erefl(d, p, mul_a_a);
    let c3c = d.lemma(
        p.add_congr,
        &[mul_a_a, mul_a_a, mul_a_nb, neg_mul_a_b, refl_aa, c3],
    );
    let proof_p = echain(
        d,
        p,
        mul_biga_a,
        &[(mul_a_biga, c1), (add_aa_anb, c2), (big_p, c3c)],
    );

    let d1 = d.lemma(p.mul_comm, &[big_a, b]);
    let d2 = d.lemma(p.left_distrib, &[b, a, nb]);
    let add_ba_bnb = cadd(d, p, mul_b_a, mul_b_nb);
    let d3 = mul_neg_equiv(d, p, b, b);
    let refl_ba = erefl(d, p, mul_b_a);
    let d3c = d.lemma(
        p.add_congr,
        &[mul_b_a, mul_b_a, mul_b_nb, neg_mul_b_b, refl_ba, d3],
    );
    let add_ba_negbb = cadd(d, p, mul_b_a, neg_mul_b_b);
    let d4 = d.lemma(p.mul_comm, &[b, a]);
    let refl_negbb = erefl(d, p, neg_mul_b_b);
    let d4c = d.lemma(
        p.add_congr,
        &[mul_b_a, mul_a_b, neg_mul_b_b, neg_mul_b_b, d4, refl_negbb],
    );
    let proof_q = echain(
        d,
        p,
        mul_biga_b,
        &[
            (mul_b_biga, d1),
            (add_ba_bnb, d2),
            (add_ba_negbb, d3c),
            (big_q, d4c),
        ],
    );

    let pq_congr = d.lemma(
        p.add_congr,
        &[mul_biga_a, big_p, mul_biga_b, big_q, proof_p, proof_q],
    );

    let cm = cancel_middle(d, p, mul_a_a, mul_a_b, mul_b_b);

    echain(
        d,
        p,
        lhs0,
        &[(target1, step1), (pq, pq_congr), (final_rhs, cm)],
    )
}

/// From `h : le y z`, `le zero (add z (neg y))`.
fn sub_nonneg_of_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    y: ExprId,
    z: ExprId,
    h: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let gap = cadd(d, p, z, ny);
    let cancelled = cadd(d, p, y, ny);

    let reflexive = d.lemma(p.le_refl, &[ny]);
    let shifted = d.lemma(p.add_le_add, &[y, z, ny, ny, h, reflexive]);
    let cancel = d.lemma(p.add_neg, &[y]);
    let gap_refl = erefl(d, p, gap);
    d.lemma(
        p.le_congr,
        &[cancelled, zero_c, gap, gap, cancel, gap_refl, shifted],
    )
}

/// From `h : le zero (add b (neg a))`, `le a b`.
fn le_of_nonneg_sub(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let gap = cadd(d, p, b, na);
    let zero_a = cadd(d, p, zero_c, a);
    let gap_a = cadd(d, p, gap, a);
    let na_a = cadd(d, p, na, a);
    let b_naa = cadd(d, p, b, na_a);
    let a_zero = cadd(d, p, a, zero_c);
    let b_zero = cadd(d, p, b, zero_c);

    let reflexive = d.lemma(p.le_refl, &[a]);
    let step1 = d.lemma(p.add_le_add, &[zero_c, gap, a, a, h, reflexive]);

    let lhs_comm = d.lemma(p.add_comm, &[zero_c, a]);
    let lhs_trim = d.lemma(p.add_zero, &[a]);
    let lhs_eq = echain(d, p, zero_a, &[(a_zero, lhs_comm), (a, lhs_trim)]);

    let rhs_assoc = d.lemma(p.add_assoc, &[b, na, a]);
    let na_a_zero = neg_add_self(d, p, a);
    let refl_b = erefl(d, p, b);
    let rhs_congr = d.lemma(p.add_congr, &[b, b, na_a, zero_c, refl_b, na_a_zero]);
    let rhs_trim = d.lemma(p.add_zero, &[b]);
    let rhs_eq = echain(
        d,
        p,
        gap_a,
        &[(b_naa, rhs_assoc), (b_zero, rhs_congr), (b, rhs_trim)],
    );

    d.lemma(p.le_congr, &[zero_a, a, gap_a, b, lhs_eq, rhs_eq, step1])
}

/// From `v_nonneg : le zero v` and `bound_nonneg : le zero bound`,
/// `le (neg v) bound`.
fn neg_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    v_nonneg: ExprId,
    bound_nonneg: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_v = cneg(d, p, v);
    let neg_zero = cneg(d, p, zero_c);

    let step = d.lemma(p.neg_le_neg, &[zero_c, v, v_nonneg]);
    let nz_eq = neg_zero_equiv(d, p);
    let refl_negv = erefl(d, p, neg_v);
    let le_negv_zero = d.lemma(
        p.le_congr,
        &[neg_v, neg_v, neg_zero, zero_c, refl_negv, nz_eq, step],
    );

    d.lemma(
        p.le_trans,
        &[neg_v, zero_c, bound, le_negv_zero, bound_nonneg],
    )
}

/// `le (mul t t) (mul (abs t) (abs t))` — squaring is dominated by squaring
/// the magnitude, via `(|t|-t)*(|t|+t) >= 0` ([`diff_of_squares`] plus
/// [`CRealPrelude::mul_nonneg`]), never deciding `t`'s sign.
fn sq_le_abs_sq(d: &mut IntDev<'_>, p: CRealPrelude, t: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let abs_t = cabs(d, p, t);
    let nt = cneg(d, p, t);
    let nnt = cneg(d, p, nt);

    let h_self_le = d.lemma(p.le_abs_self, &[t]);
    let h1 = sub_nonneg_of_le(d, p, t, abs_t, h_self_le);

    let h_neg_le = d.lemma(p.neg_le_abs, &[t]);
    let h2a = sub_nonneg_of_le(d, p, nt, abs_t, h_neg_le);

    let nn = double_neg(d, p, t);
    let abs_t_nnt = cadd(d, p, abs_t, nnt);
    let abs_t_t = cadd(d, p, abs_t, t);
    let refl_abst = erefl(d, p, abs_t);
    let eqb = d.lemma(p.add_congr, &[abs_t, abs_t, nnt, t, refl_abst, nn]);

    let refl_zero = erefl(d, p, zero_c);
    let h2 = d.lemma(
        p.le_congr,
        &[zero_c, zero_c, abs_t_nnt, abs_t_t, refl_zero, eqb, h2a],
    );

    let abs_t_nt = cadd(d, p, abs_t, nt);
    let dos = diff_of_squares(d, p, abs_t, t);
    let prod = cmul(d, p, abs_t_nt, abs_t_t);
    let mn = d.lemma(p.mul_nonneg, &[abs_t_nt, abs_t_t, h1, h2]);

    let mul_abst_abst = cmul(d, p, abs_t, abs_t);
    let mul_t_t = cmul(d, p, t, t);
    let neg_mul_t_t = cneg(d, p, mul_t_t);
    let diffsq_rhs = cadd(d, p, mul_abst_abst, neg_mul_t_t);

    let h_diffsq_nonneg = d.lemma(
        p.le_congr,
        &[zero_c, zero_c, prod, diffsq_rhs, refl_zero, dos, mn],
    );

    le_of_nonneg_sub(d, p, mul_t_t, mul_abst_abst, h_diffsq_nonneg)
}

/// `Equiv (mul (neg a) b) (neg (mul a b))` — the mirror of [`mul_neg_equiv`]
/// (which negates the *second* factor), built the same way: commute, apply
/// [`mul_neg_equiv`], commute back under `neg_congr`.
fn neg_mul_equiv_left(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let lhs = cmul(d, p, na, b);
    let b_na = cmul(d, p, b, na);
    let c1 = d.lemma(p.mul_comm, &[na, b]); // lhs ~ b_na

    let ba = cmul(d, p, b, a);
    let neg_ba = cneg(d, p, ba);
    let c2 = mul_neg_equiv(d, p, b, a); // b_na ~ neg_ba

    let ab = cmul(d, p, a, b);
    let neg_ab = cneg(d, p, ab);
    let c3a = d.lemma(p.mul_comm, &[b, a]); // ba ~ ab
    let c3 = d.lemma(p.neg_congr, &[ba, ab, c3a]); // neg_ba ~ neg_ab

    echain(d, p, lhs, &[(b_na, c1), (neg_ba, c2), (neg_ab, c3)])
}

// `right_distrib` (`Equiv (mul (add a b) c) (add (mul a c) (mul b c))`) and
// `add4_comm` (`Equiv (add (add a b) (add c dd)) (add (add a c) (add b dd))`)
// used to be rebuilt here, byte-for-byte identical to `creal/power.rs`'s and
// `creal/series.rs`'s own private copies respectively — each one duplicated
// only because the other file's copy was private to that module. Both are
// now `pub(super)` in `creal/ring_helpers.rs`, imported above, and this file
// calls the shared versions directly.

/// `le (abs (add a b)) (add (abs a) (abs b))` — the two-term triangle
/// inequality, from [`CRealPrelude::abs_le`] with
/// [`CRealPrelude::add_le_add`]/[`CRealPrelude::le_abs_self`] for the lower
/// branch and [`neg_add_distrib`] plus [`CRealPrelude::neg_le_abs`] for the
/// upper (negated) branch. Copied from `creal/series.rs`'s own private
/// `abs_add_le`, using this file's own `neg_add_distrib` in place of
/// `series.rs`'s `neg_add` (the identical statement, built earlier in this
/// file for `sq_le_abs_sq`).
fn abs_add_le(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let s = cadd(d, p, a, b);
    let abs_a = cabs(d, p, a);
    let abs_b = cabs(d, p, b);
    let bound = cadd(d, p, abs_a, abs_b);

    // premise1 : le (add a b) (add (abs a) (abs b))
    let le_a = d.lemma(p.le_abs_self, &[a]);
    let le_b = d.lemma(p.le_abs_self, &[b]);
    let premise1 = d.lemma(p.add_le_add, &[a, abs_a, b, abs_b, le_a, le_b]);

    // premise2 : le (neg (add a b)) (add (abs a) (abs b))
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let t = cadd(d, p, na, nb);
    let ns = cneg(d, p, s);
    let na_eq = neg_add_distrib(d, p, a, b); // ns ~ t
    let step1 = d.lemma(p.le_of_equiv, &[ns, t, na_eq]); // le ns t
    let nle_a = d.lemma(p.neg_le_abs, &[a]); // le na abs_a
    let nle_b = d.lemma(p.neg_le_abs, &[b]); // le nb abs_b
    let step2 = d.lemma(p.add_le_add, &[na, abs_a, nb, abs_b, nle_a, nle_b]); // le t bound
    let premise2 = d.lemma(p.le_trans, &[ns, t, bound, step1, step2]);

    d.lemma(p.abs_le, &[s, bound, premise1, premise2])
}

/// From `eq_vw : Equiv v w` and `h_w : le (abs w) bound`, derive `le (abs v)
/// bound` — [`CRealPrelude::abs_congr`] plus [`CRealPrelude::le_congr`],
/// the general "the bound transports along an `Equiv` on the value" step
/// every witness in this file that reduces its own error term to a simpler
/// shape needs at least once.
fn abs_le_of_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    w: ExprId,
    bound: ExprId,
    eq_vw: ExprId,
    h_w: ExprId,
) -> ExprId {
    let abs_v = cabs(d, p, v);
    let abs_w = cabs(d, p, w);
    let abs_eq = d.lemma(p.abs_congr, &[v, w, eq_vw]); // Equiv abs_v abs_w
    let abs_eq_symm = esymm(d, p, abs_v, abs_w, abs_eq); // Equiv abs_w abs_v
    let refl_bound = erefl(d, p, bound);
    d.lemma(
        p.le_congr,
        &[abs_w, abs_v, bound, bound, abs_eq_symm, refl_bound, h_w],
    )
}

/// From `h : le (abs x) bound`, derive `le (abs (neg x)) bound` — `|−x| =
/// |x|` is a structural identity (true regardless of `x`'s sign, never
/// decided), so this is NOT an instance of [`abs_le_of_equiv`] (`neg x` is
/// not `Equiv`-equal to `x` in general): it goes through [`abs_le`] directly,
/// bounding `neg x` (via [`CRealPrelude::neg_le_abs`]) and `neg (neg x)`
/// (via [`double_neg`] transporting [`CRealPrelude::le_abs_self`]) each
/// against the same `bound` `h` already supplies for `abs x`.
fn le_abs_neg_of_le_abs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    bound: ExprId,
    h: ExprId,
) -> ExprId {
    let abs_x = cabs(d, p, x);
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);

    // le (neg x) bound
    let nle = d.lemma(p.neg_le_abs, &[x]); // le nx abs_x
    let upper = d.lemma(p.le_trans, &[nx, abs_x, bound, nle, h]);

    // le (neg (neg x)) bound, via double_neg transporting `le x bound`.
    let le_x_bound = {
        let sle = d.lemma(p.le_abs_self, &[x]); // le x abs_x
        d.lemma(p.le_trans, &[x, abs_x, bound, sle, h])
    };
    let nn = double_neg(d, p, x); // Equiv nnx x
    let nn_symm = esymm(d, p, nnx, x, nn); // Equiv x nnx
    let refl_bound = erefl(d, p, bound);
    let lower = d.lemma(
        p.le_congr,
        &[x, nnx, bound, bound, nn_symm, refl_bound, le_x_bound],
    );

    d.lemma(p.abs_le, &[nx, bound, upper, lower])
}

// --- the two-variable product-of-bounds lemma ---------------------------------
//
// `CReal.abs_mul_le_of_bounds` — see the module documentation's "product
// rule" section and [`CRealPrelude::abs_mul_le_of_bounds`] for the argument.
// The helpers below are private to this block; nothing outside
// `declare_abs_mul_le_of_bounds` calls them.

/// From `h : le (neg x) bound`, derive `le zero (add bound x)` — the
/// `bound + x >= 0` half of a magnitude bound, mirroring [`sub_nonneg_of_le`]
/// (`bound - x >= 0` from `le x bound`) through [`double_neg`].
fn plus_nonneg_of_neg_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    bound: ExprId,
    h: ExprId,
) -> ExprId {
    let nx = cneg(d, p, x);
    let pre = sub_nonneg_of_le(d, p, nx, bound, h); // le zero (add bound (neg (neg x)))
    let nnx = cneg(d, p, nx);
    let nn = double_neg(d, p, x); // Equiv nnx x
    let refl_bound = erefl(d, p, bound);
    let congr = d.lemma(p.add_congr, &[bound, bound, nnx, x, refl_bound, nn]);
    let zero_c = czero(d, p);
    let refl_zero = erefl(d, p, zero_c);
    let add_bound_nnx = cadd(d, p, bound, nnx);
    let add_bound_x = cadd(d, p, bound, x);
    d.lemma(
        p.le_congr,
        &[
            zero_c,
            zero_c,
            add_bound_nnx,
            add_bound_x,
            refl_zero,
            congr,
            pre,
        ],
    )
}

/// `Equiv (add (add x (neg y)) (add x y)) (add x x)` — `(x−y)+(x+y) ~ x+x`,
/// the `y`-cancelling half of the two-variable product-of-bounds identity
/// [`abs_mul_le_of_bounds_body`] needs. Same style as [`cancel_middle`].
fn double_first(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let x_ny = cadd(d, p, x, ny);
    let x_y = cadd(d, p, x, y);
    let lhs = cadd(d, p, x_ny, x_y);
    let ny_xy = cadd(d, p, ny, x_y);
    let x_plus_nyxy = cadd(d, p, x, ny_xy);
    let x_x = cadd(d, p, x, x);

    // lhs ~ x + (ny + x_y)
    let step_assoc = d.lemma(p.add_assoc, &[x, ny, x_y]);

    // ny_xy ~ x
    let ny_x = cadd(d, p, ny, x);
    let ny_x_y = cadd(d, p, ny_x, y);
    let assoc2 = d.lemma(p.add_assoc, &[ny, x, y]); // ny_x_y ~ ny_xy
    let step_b1 = esymm(d, p, ny_x_y, ny_xy, assoc2); // ny_xy ~ ny_x_y

    let comm1 = d.lemma(p.add_comm, &[ny, x]); // ny_x ~ x_ny
    let refl_y = erefl(d, p, y);
    let x_ny_y = cadd(d, p, x_ny, y);
    let congr1 = d.lemma(p.add_congr, &[ny_x, x_ny, y, y, comm1, refl_y]); // ny_x_y ~ x_ny_y

    let ny_y = cadd(d, p, ny, y);
    let x_plus_nyy = cadd(d, p, x, ny_y);
    let assoc3 = d.lemma(p.add_assoc, &[x, ny, y]); // x_ny_y ~ x_plus_nyy

    let zero_c = czero(d, p);
    let nas = neg_add_self(d, p, y); // Equiv ny_y zero
    let refl_x = erefl(d, p, x);
    let x_zero = cadd(d, p, x, zero_c);
    let congr2 = d.lemma(p.add_congr, &[x, x, ny_y, zero_c, refl_x, nas]); // x_plus_nyy ~ x_zero

    let az = d.lemma(p.add_zero, &[x]); // x_zero ~ x

    let ny_xy_to_x = echain(
        d,
        p,
        ny_xy,
        &[
            (ny_x_y, step_b1),
            (x_ny_y, congr1),
            (x_plus_nyy, assoc3),
            (x_zero, congr2),
            (x, az),
        ],
    );

    let congr_final = d.lemma(p.add_congr, &[x, x, ny_xy, x, refl_x, ny_xy_to_x]); // x_plus_nyxy ~ x_x

    echain(d, p, lhs, &[(x_plus_nyxy, step_assoc), (x_x, congr_final)])
}

/// `Equiv (add (add x y) (add (neg x) y)) (add y y)` — `(x+y)+(−x+y) ~ y+y`,
/// [`double_first`] with the two summands and the two addends each commuted.
fn double_second(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let x_y = cadd(d, p, x, y);
    let nx_y = cadd(d, p, nx, y);
    let lhs = cadd(d, p, x_y, nx_y);

    let y_x = cadd(d, p, y, x);
    let y_nx = cadd(d, p, y, nx);
    let comm_a = d.lemma(p.add_comm, &[x, y]); // x_y ~ y_x
    let comm_b = d.lemma(p.add_comm, &[nx, y]); // nx_y ~ y_nx
    let rhs1 = cadd(d, p, y_x, y_nx);
    let step1 = d.lemma(p.add_congr, &[x_y, y_x, nx_y, y_nx, comm_a, comm_b]); // lhs ~ rhs1

    let rhs2 = cadd(d, p, y_nx, y_x);
    let comm_outer = d.lemma(p.add_comm, &[y_x, y_nx]); // rhs1 ~ rhs2

    let df = double_first(d, p, y, x); // Equiv rhs2 (add y y)
    let y_y = cadd(d, p, y, y);

    echain(d, p, lhs, &[(rhs1, step1), (rhs2, comm_outer), (y_y, df)])
}

/// `(half, half_nonneg, proof)` — `half := ofRat (natDivSucc 1 1)`, a proof
/// it is nonnegative ([`nonneg_rat_bound`]), and `proof : Equiv (add half
/// half) CReal.one`.
///
/// Closed through `Rat.natDivSucc_add`/`Rat.natDivSucc_halve` — the same
/// fusion [`declare_has_derivative_add`] uses for `1/(2e+2)+1/(2e+2) ~
/// 1/(e+1)`, here at the literal `e := 0` — plus the kernel's own reduction
/// of `Rat.natDivSucc 1 0` against `Rat.one`: `CReal.one` is *defined* as
/// `CReal.ofRat Rat.one` with a `Regular` (unfoldable) reducibility hint
/// (`declare_constants`), so the closing step needs no separate
/// `Rat.natDivSucc 1 0 = Rat.one` lemma.
fn half_and_double_one(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId, ExprId) {
    let one_nat = d.num(1);
    let (half, half_nonneg) = nonneg_rat_bound(d, p, 1, one_nat);
    let q = div_succ(d, p, 1, one_nat); // natDivSucc 1 1

    let half_half = cadd(d, p, half, half);
    let radd_qq = radd(d, q, q);
    let of_rat_add_proof = d.lemma(p.of_rat_add, &[q, q]);
    // Equiv half_half (ofRat radd_qq)

    let eq1 = d.lemma(p.rat.nat_div_succ_add, &[one_nat, one_nat, one_nat]);
    // Eq (radd q q) (natDivSucc (add 1 1) 1)
    let combined = d.add(one_nat, one_nat);
    let two_over_1 = d.const_app(p.rat.nat_div_succ, &[combined, one_nat]);
    let step_a = rat_eq_rewrite(d, radd_qq, two_over_1, eq1, of_rat_add_proof, &|d, t| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[half_half, oft])
    });
    // Equiv half_half (ofRat two_over_1)

    let zero_nat = d.num(0);
    let eq2 = d.lemma(p.rat.nat_div_succ_halve, &[zero_nat]);
    // Eq (natDivSucc 2 (succ (mul 2 0))) (natDivSucc 1 0)
    let one_over_0 = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
    let step_b = rat_eq_rewrite(d, two_over_1, one_over_0, eq2, step_a, &|d, t| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[half_half, oft])
    });
    // Equiv half_half (ofRat one_over_0); `ofRat one_over_0` is defeq
    // `CReal.one` (see the doc comment above), so this is used directly
    // wherever `Equiv (add half half) one` is needed.

    (half, half_nonneg, step_b)
}

/// From `h : le zero (add v v)`, derive `le zero v` — halving a
/// nonnegativity fact by multiplying through by the literal constant `1/2`
/// ([`half_and_double_one`]), never deciding `v`'s sign.
fn nonneg_of_double_nonneg(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId, h: ExprId) -> ExprId {
    let (half, half_nonneg, half_double_one) = half_and_double_one(d, p);
    let v_v = cadd(d, p, v, v);
    let zero_c = czero(d, p);

    let step1 = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[half, zero_c, v_v, half_nonneg, h],
    );
    // le (mul half zero) (mul half v_v)
    let mul_half_zero = cmul(d, p, half, zero_c);
    let mz = d.lemma(p.mul_zero, &[half]); // Equiv mul_half_zero zero
    let mul_half_vv = cmul(d, p, half, v_v);
    let refl_mhv = erefl(d, p, mul_half_vv);
    let transported = d.lemma(
        p.le_congr,
        &[
            mul_half_zero,
            zero_c,
            mul_half_vv,
            mul_half_vv,
            mz,
            refl_mhv,
            step1,
        ],
    ); // le zero mul_half_vv

    // mul_half_vv ~ v
    let ld = d.lemma(p.left_distrib, &[half, v, v]);
    // Equiv mul_half_vv (add (mul half v) (mul half v))
    let mul_half_v = cmul(d, p, half, v);
    let sum_mhv = cadd(d, p, mul_half_v, mul_half_v);

    let one_c = d.kernel().const_(p.one, vec![]);
    let half_half = cadd(d, p, half, half);
    let rd = right_distrib(d, p, half, half, v);
    // Equiv (mul half_half v) sum_mhv
    let mul_double_v = cmul(d, p, half_half, v);
    let rd_symm = esymm(d, p, mul_double_v, sum_mhv, rd); // Equiv sum_mhv mul_double_v

    let mul_one_v = cmul(d, p, one_c, v);
    let refl_v = erefl(d, p, v);
    let congr_one = d.lemma(
        p.mul_congr,
        &[half_half, one_c, v, v, half_double_one, refl_v],
    ); // Equiv mul_double_v mul_one_v

    let mul_v_one = cmul(d, p, v, one_c);
    let comm_v1 = d.lemma(p.mul_comm, &[one_c, v]); // Equiv mul_one_v mul_v_one
    let mo = d.lemma(p.mul_one, &[v]); // Equiv mul_v_one v

    let sum_to_v = echain(
        d,
        p,
        sum_mhv,
        &[
            (mul_double_v, rd_symm),
            (mul_one_v, congr_one),
            (mul_v_one, comm_v1),
            (v, mo),
        ],
    );

    let mhv_to_v = echain(d, p, mul_half_vv, &[(sum_mhv, ld), (v, sum_to_v)]);

    let refl_zero = erefl(d, p, zero_c);
    d.lemma(
        p.le_congr,
        &[
            zero_c,
            zero_c,
            mul_half_vv,
            v,
            refl_zero,
            mhv_to_v,
            transported,
        ],
    )
}

/// `P1 := mul (add big_b (neg x)) (add small_b t)`, expanded:
/// `Equiv P1 (add (add (mul big_b small_b) (neg (mul x small_b))) (add (mul
/// big_b t) (neg (mul x t))))` — via [`p.left_distrib`]/[`right_distrib`]/
/// [`neg_mul_equiv_left`]. Returns `(P1, a_term, b_term, proof)`.
#[allow(clippy::similar_names)]
fn expand_p1(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    big_b: ExprId,
    x: ExprId,
    small_b: ExprId,
    t: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let neg_x = cneg(d, p, x);
    let big_a = cadd(d, p, big_b, neg_x); // B - x
    let b_plus_t = cadd(d, p, small_b, t);
    let p1 = cmul(d, p, big_a, b_plus_t);

    let mul_biga_b = cmul(d, p, big_a, small_b);
    let mul_biga_t = cmul(d, p, big_a, t);
    let ld = d.lemma(p.left_distrib, &[big_a, small_b, t]);
    // Equiv p1 (add mul_biga_b mul_biga_t)

    // mul_biga_b ~ a_term := add (mul B b) (neg (mul x b))
    let mul_bb = cmul(d, p, big_b, small_b);
    let mul_xb = cmul(d, p, x, small_b);
    let neg_mul_xb = cneg(d, p, mul_xb);
    let a_term = cadd(d, p, mul_bb, neg_mul_xb);
    let rd_b = right_distrib(d, p, big_b, neg_x, small_b);
    // Equiv mul_biga_b (add mul_bb (mul neg_x small_b))
    let mul_negx_b = cmul(d, p, neg_x, small_b);
    let nme_b = neg_mul_equiv_left(d, p, x, small_b); // Equiv mul_negx_b neg_mul_xb
    let refl_bb = erefl(d, p, mul_bb);
    let congr_b = d.lemma(
        p.add_congr,
        &[mul_bb, mul_bb, mul_negx_b, neg_mul_xb, refl_bb, nme_b],
    );
    let chain_b_target = cadd(d, p, mul_bb, mul_negx_b);
    let chain_b = echain(
        d,
        p,
        mul_biga_b,
        &[(chain_b_target, rd_b), (a_term, congr_b)],
    );

    // mul_biga_t ~ b_term := add (mul B t) (neg (mul x t))
    let mul_bt = cmul(d, p, big_b, t);
    let mul_xt = cmul(d, p, x, t);
    let neg_mul_xt = cneg(d, p, mul_xt);
    let b_term = cadd(d, p, mul_bt, neg_mul_xt);
    let rd_t = right_distrib(d, p, big_b, neg_x, t);
    let mul_negx_t = cmul(d, p, neg_x, t);
    let nme_t = neg_mul_equiv_left(d, p, x, t);
    let refl_bt = erefl(d, p, mul_bt);
    let congr_t = d.lemma(
        p.add_congr,
        &[mul_bt, mul_bt, mul_negx_t, neg_mul_xt, refl_bt, nme_t],
    );
    let chain_t_target = cadd(d, p, mul_bt, mul_negx_t);
    let chain_t = echain(
        d,
        p,
        mul_biga_t,
        &[(chain_t_target, rd_t), (b_term, congr_t)],
    );

    let full_congr = d.lemma(
        p.add_congr,
        &[mul_biga_b, a_term, mul_biga_t, b_term, chain_b, chain_t],
    );
    let expanded = cadd(d, p, a_term, b_term);
    let ld_target = cadd(d, p, mul_biga_b, mul_biga_t);
    let proof = echain(d, p, p1, &[(ld_target, ld), (expanded, full_congr)]);

    (p1, a_term, b_term, proof)
}

/// `P2 := mul (add big_b x) (add small_b (neg t))`, expanded: `Equiv P2 (add
/// (add (mul big_b small_b) (mul x small_b)) (add (neg (mul big_b t)) (neg
/// (mul x t))))`. Returns `(P2, c_term, d_term, proof)`.
#[allow(clippy::similar_names)]
fn expand_p2(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    big_b: ExprId,
    x: ExprId,
    small_b: ExprId,
    t: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let big_c = cadd(d, p, big_b, x); // B + x
    let neg_t = cneg(d, p, t);
    let b_minus_t = cadd(d, p, small_b, neg_t);
    let p2 = cmul(d, p, big_c, b_minus_t);

    let mul_bigc_b = cmul(d, p, big_c, small_b);
    let mul_bigc_negt = cmul(d, p, big_c, neg_t);
    let ld = d.lemma(p.left_distrib, &[big_c, small_b, neg_t]);
    // Equiv p2 (add mul_bigc_b mul_bigc_negt)

    // mul_bigc_b ~ c_term := add (mul B b) (mul x b)  -- right_distrib lands
    // exactly here, no further congruence step needed.
    let mul_bb = cmul(d, p, big_b, small_b);
    let mul_xb = cmul(d, p, x, small_b);
    let c_term = cadd(d, p, mul_bb, mul_xb);
    let chain_b = right_distrib(d, p, big_b, x, small_b); // Equiv mul_bigc_b c_term

    // mul_bigc_negt ~ d_term := add (neg (mul B t)) (neg (mul x t))
    let mul_bt = cmul(d, p, big_b, t);
    let mul_xt = cmul(d, p, x, t);
    let neg_bt = cneg(d, p, mul_bt);
    let neg_xt = cneg(d, p, mul_xt);
    let d_term = cadd(d, p, neg_bt, neg_xt);
    let rd_negt = right_distrib(d, p, big_b, x, neg_t);
    // Equiv mul_bigc_negt (add (mul B neg_t) (mul x neg_t))
    let mul_b_negt = cmul(d, p, big_b, neg_t);
    let mul_x_negt = cmul(d, p, x, neg_t);
    let mne_b = mul_neg_equiv(d, p, big_b, t); // Equiv mul_b_negt neg_bt
    let mne_x = mul_neg_equiv(d, p, x, t); // Equiv mul_x_negt neg_xt
    let congr_negt = d.lemma(
        p.add_congr,
        &[mul_b_negt, neg_bt, mul_x_negt, neg_xt, mne_b, mne_x],
    );
    let rd_negt_target = cadd(d, p, mul_b_negt, mul_x_negt);
    let chain_negt = echain(
        d,
        p,
        mul_bigc_negt,
        &[(rd_negt_target, rd_negt), (d_term, congr_negt)],
    );

    let full_congr = d.lemma(
        p.add_congr,
        &[
            mul_bigc_b,
            c_term,
            mul_bigc_negt,
            d_term,
            chain_b,
            chain_negt,
        ],
    );
    let expanded = cadd(d, p, c_term, d_term);
    let ld_target = cadd(d, p, mul_bigc_b, mul_bigc_negt);
    let proof = echain(d, p, p2, &[(ld_target, ld), (expanded, full_congr)]);

    (p2, c_term, d_term, proof)
}

/// `le (mul x t) (mul big_b small_b)` from `le x big_b`, `le (neg x)
/// big_b`, `le t small_b`, `le (neg t) small_b` — the one-sided half of
/// [`abs_mul_le_of_bounds_body`], built from the two-identity route: `2·(B·b
/// − x·t) = (B−x)·(b+t) + (B+x)·(b−t)`, each summand a product of two
/// nonnegatives ([`expand_p1`]/[`expand_p2`] plus [`double_first`]/
/// [`double_second`] to cancel the cross terms), halved by
/// [`nonneg_of_double_nonneg`], never deciding `x`'s or `t`'s sign.
#[allow(clippy::too_many_arguments, clippy::similar_names)]
fn upper_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    t: ExprId,
    big_b: ExprId,
    small_b: ExprId,
    x_le_b: ExprId,
    negx_le_b: ExprId,
    t_le_b: ExprId,
    negt_le_b: ExprId,
) -> ExprId {
    let b_minus_x_nonneg = sub_nonneg_of_le(d, p, x, big_b, x_le_b);
    let b_plus_x_nonneg = plus_nonneg_of_neg_le(d, p, x, big_b, negx_le_b);
    let smallb_minus_t_nonneg = sub_nonneg_of_le(d, p, t, small_b, t_le_b);
    let smallb_plus_t_nonneg = plus_nonneg_of_neg_le(d, p, t, small_b, negt_le_b);

    let (p1, a_term, b_term, p1_expand) = expand_p1(d, p, big_b, x, small_b, t);
    let (p2, c_term, d_term, p2_expand) = expand_p2(d, p, big_b, x, small_b, t);

    let neg_x = cneg(d, p, x);
    let big_a = cadd(d, p, big_b, neg_x);
    let b_plus_t = cadd(d, p, small_b, t);
    let p1_nonneg = d.lemma(
        p.mul_nonneg,
        &[big_a, b_plus_t, b_minus_x_nonneg, smallb_plus_t_nonneg],
    );

    let big_c = cadd(d, p, big_b, x);
    let neg_t = cneg(d, p, t);
    let b_minus_t = cadd(d, p, small_b, neg_t);
    let p2_nonneg = d.lemma(
        p.mul_nonneg,
        &[big_c, b_minus_t, b_plus_x_nonneg, smallb_minus_t_nonneg],
    );

    let zero_c = czero(d, p);
    let sum_le = d.lemma(
        p.add_le_add,
        &[zero_c, p1, zero_c, p2, p1_nonneg, p2_nonneg],
    );
    // le (add zero zero) (add p1 p2)
    let zero_zero = cadd(d, p, zero_c, zero_c);
    let az = d.lemma(p.add_zero, &[zero_c]); // Equiv zero_zero zero_c
    let p1p2 = cadd(d, p, p1, p2);
    let refl_p1p2 = erefl(d, p, p1p2);
    let p1p2_nonneg = d.lemma(
        p.le_congr,
        &[zero_zero, zero_c, p1p2, p1p2, az, refl_p1p2, sum_le],
    ); // le zero p1p2

    let mul_bb = cmul(d, p, big_b, small_b);
    let mul_xt = cmul(d, p, x, t);
    let neg_xt = cneg(d, p, mul_xt);
    let v = cadd(d, p, mul_bb, neg_xt);

    // p1p2 ~ add (add a_term b_term) (add c_term d_term)
    let ab_sum = cadd(d, p, a_term, b_term);
    let cd_sum = cadd(d, p, c_term, d_term);
    let stage1 = cadd(d, p, ab_sum, cd_sum);
    let congr1 = d.lemma(p.add_congr, &[p1, ab_sum, p2, cd_sum, p1_expand, p2_expand]);

    // ~ add (add a_term c_term) (add b_term d_term)
    let (stage2, proof_ac1) = add4_comm(d, p, a_term, b_term, c_term, d_term);

    // a_term + c_term ~ add mul_bb mul_bb ; b_term + d_term ~ add neg_xt neg_xt
    let mul_xb = cmul(d, p, x, small_b);
    let mul_bt = cmul(d, p, big_b, t);
    let df1 = double_first(d, p, mul_bb, mul_xb); // Equiv (add a_term c_term) (add mul_bb mul_bb)
    let df2 = double_second(d, p, mul_bt, neg_xt); // Equiv (add b_term d_term) (add neg_xt neg_xt)

    let ac_sum = cadd(d, p, a_term, c_term);
    let bd_sum = cadd(d, p, b_term, d_term);
    let bb_bb = cadd(d, p, mul_bb, mul_bb);
    let negxt_negxt = cadd(d, p, neg_xt, neg_xt);
    let stage3 = cadd(d, p, bb_bb, negxt_negxt);
    let congr2 = d.lemma(p.add_congr, &[ac_sum, bb_bb, bd_sum, negxt_negxt, df1, df2]);

    // ~ add (add mul_bb neg_xt) (add mul_bb neg_xt) = add v v
    let (stage4, proof_ac2) = add4_comm(d, p, mul_bb, mul_bb, neg_xt, neg_xt);

    let double_identity = echain(
        d,
        p,
        p1p2,
        &[
            (stage1, congr1),
            (stage2, proof_ac1),
            (stage3, congr2),
            (stage4, proof_ac2),
        ],
    );

    let v_v = cadd(d, p, v, v);
    let refl_zero = erefl(d, p, zero_c);
    let v_v_nonneg = d.lemma(
        p.le_congr,
        &[
            zero_c,
            zero_c,
            p1p2,
            v_v,
            refl_zero,
            double_identity,
            p1p2_nonneg,
        ],
    );

    let v_nonneg = nonneg_of_double_nonneg(d, p, v, v_v_nonneg);

    le_of_nonneg_sub(d, p, mul_xt, mul_bb, v_nonneg)
}

/// `le (abs (mul c t)) (mul big_b small_b)` from `le (abs c) big_b` and `le
/// (abs t) small_b` — [`CRealPrelude::abs_mul_le_of_bounds`]'s body. Gets the
/// lower bound for free from [`upper_bound`] applied at `neg c` in place of
/// `c`, transported through [`neg_mul_equiv_left`], rather than re-deriving a
/// second two-identity argument.
fn abs_mul_le_of_bounds_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    t: ExprId,
    big_b: ExprId,
    small_b: ExprId,
    h_c: ExprId,
    h_t: ExprId,
) -> ExprId {
    let abs_c = cabs(d, p, c);
    let c_le_absc = d.lemma(p.le_abs_self, &[c]);
    let c_le_b = d.lemma(p.le_trans, &[c, abs_c, big_b, c_le_absc, h_c]);
    let neg_c = cneg(d, p, c);
    let negc_le_absc = d.lemma(p.neg_le_abs, &[c]);
    let negc_le_b = d.lemma(p.le_trans, &[neg_c, abs_c, big_b, negc_le_absc, h_c]);

    let abs_t = cabs(d, p, t);
    let t_le_abst = d.lemma(p.le_abs_self, &[t]);
    let t_le_b = d.lemma(p.le_trans, &[t, abs_t, small_b, t_le_abst, h_t]);
    let neg_t = cneg(d, p, t);
    let negt_le_abst = d.lemma(p.neg_le_abs, &[t]);
    let negt_le_b = d.lemma(p.le_trans, &[neg_t, abs_t, small_b, negt_le_abst, h_t]);

    let upper = upper_bound(
        d, p, c, t, big_b, small_b, c_le_b, negc_le_b, t_le_b, negt_le_b,
    );
    // le (mul c t) (mul big_b small_b)

    // le (neg c) big_b [= negc_le_b] and le (neg (neg c)) big_b [needed].
    let nnc = cneg(d, p, neg_c);
    let nn = double_neg(d, p, c); // Equiv nnc c
    let nn_symm = esymm(d, p, nnc, c, nn); // Equiv c nnc
    let refl_b = erefl(d, p, big_b);
    let neg_neg_c_le_b = d.lemma(p.le_congr, &[c, nnc, big_b, big_b, nn_symm, refl_b, c_le_b]);

    let upper_neg = upper_bound(
        d,
        p,
        neg_c,
        t,
        big_b,
        small_b,
        negc_le_b,
        neg_neg_c_le_b,
        t_le_b,
        negt_le_b,
    );
    // le (mul neg_c t) (mul big_b small_b)

    let mul_negc_t = cmul(d, p, neg_c, t);
    let mul_bb = cmul(d, p, big_b, small_b);
    // upper_neg : le mul_negc_t mul_bb, directly -- upper_bound returns `le
    // (mul x t) (mul B b)` with no `abs` in it, so no `le_abs_self`/`le_trans`
    // detour through `abs mul_negc_t` is needed (or well-typed) here.

    let mul_ct = cmul(d, p, c, t);
    let neg_mul_ct = cneg(d, p, mul_ct);
    let nme = neg_mul_equiv_left(d, p, c, t); // Equiv mul_negc_t neg_mul_ct
    let refl_bb = erefl(d, p, mul_bb);
    let lower = d.lemma(
        p.le_congr,
        &[
            mul_negc_t, neg_mul_ct, mul_bb, mul_bb, nme, refl_bb, upper_neg,
        ],
    ); // le neg_mul_ct mul_bb

    d.lemma(p.abs_le, &[mul_ct, mul_bb, upper, lower])
}

/// `CReal.abs_mul_le_of_bounds : forall c t B b, le (abs c) B -> le (abs t)
/// b -> le (abs (mul c t)) (mul B b)`. See
/// [`CRealPrelude::abs_mul_le_of_bounds`].
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_abs_mul_le_of_bounds(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let big_b_fv = d.fresh_fvar();
    let big_b = d.kernel().fvar(big_b_fv);
    let small_b_fv = d.fresh_fvar();
    let small_b = d.kernel().fvar(small_b_fv);

    let abs_c = cabs(d, p, c);
    let abs_t = cabs(d, p, t);
    let hc_ty = d.const_app(p.le, &[abs_c, big_b]);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let ht_ty = d.const_app(p.le, &[abs_t, small_b]);
    let ht_fv = d.fresh_fvar();
    let ht = d.kernel().fvar(ht_fv);

    let body = abs_mul_le_of_bounds_body(d, p, c, t, big_b, small_b, hc, ht);

    let value = {
        let with_ht = d.lam_fv(ht_fv, ht_ty, body);
        let with_hc = d.lam_fv(hc_fv, hc_ty, with_ht);
        let with_smallb = d.lam_fv(small_b_fv, carrier, with_hc);
        let with_bigb = d.lam_fv(big_b_fv, carrier, with_smallb);
        let with_t = d.lam_fv(t_fv, carrier, with_bigb);
        d.lam_fv(c_fv, carrier, with_t)
    };
    let ty = {
        let mul_ct = cmul(d, p, c, t);
        let mul_bb = cmul(d, p, big_b, small_b);
        let abs_mul_ct = cabs(d, p, mul_ct);
        let conclusion = d.const_app(p.le, &[abs_mul_ct, mul_bb]);
        let after_ht = d.arrow(ht_ty, conclusion);
        let after_hc = d.arrow(hc_ty, after_ht);
        let with_smallb = d.pi_fv(small_b_fv, carrier, after_hc);
        let with_bigb = d.pi_fv(big_b_fv, carrier, with_smallb);
        let with_t = d.pi_fv(t_fv, carrier, with_bigb);
        d.pi_fv(c_fv, carrier, with_t)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.abs_mul_le_of_bounds,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the carrier --------------------------------------------------------------

/// `CReal.HasDerivativeOn (F F' : CReal -> CReal) (a b : CReal) : Type :=
///   mk (modulus : Nat -> Nat) (spec : ...)`.
///
/// A one-constructor inductive with four leading parameters (`F, F', a, b`)
/// — genuinely parametric, exactly one level over
/// [`super::uniform_continuity::declare_carrier`]'s own three-parameter
/// shape. See the module documentation for why the data field is
/// unavoidable.
fn declare_carrier(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // ty := Π (F F' : CReal→CReal) (a b : CReal), Type 0.
    let ty = {
        let f_fv = d.fresh_fvar();
        let fp_fv = d.fresh_fvar();
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let with_b = d.pi_fv(b_fv, carrier, type0);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_fp)
    };

    // mk_ty := Π (F F' a b) (modulus : Nat → Nat) (spec : deriv_spec_body …),
    //   HasDerivativeOn F F' a b.
    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let mod_fv = d.fresh_fvar();
        let modulus = d.kernel().fvar(mod_fv);

        let spec_ty = deriv_spec_body(d, p, f, fp, a, b, modulus);
        let result = hd_ty(d, p, f, fp, a, b);

        let with_spec = d.arrow(spec_ty, result);
        let with_mod = d.pi_fv(mod_fv, nat_fn, with_spec);
        let with_b = d.pi_fv(b_fv, carrier, with_mod);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_fp)
    };

    d.kernel()
        .add_inductive(p.has_derivative_on, &[], 4, ty, &[(p.hd_mk, mk_ty)])
}

/// The two projections: the modulus (large elimination, into `Type 0`) and
/// its spec (into `Prop`, with the motive at a witness `u` reading `u`'s own
/// modulus) — the identical shape
/// [`super::uniform_continuity::declare_projections`] uses one parameter
/// over.
fn declare_projections(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();

    // modulus : ∀ F F' a b, HasDerivativeOn F F' a b → Nat → Nat
    //   := fun F F' a b u => HasDerivativeOn.rec F F' a b (fun _ => Nat → Nat)
    //        (fun modulus _ => modulus) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_hd = hd_ty(d, p, f, fp, a, b);

        let motive = d
            .kernel()
            .lam(anon, carrier_hd, nat_fn, crate::BinderInfo::Default);
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = deriv_spec_body(d, p, f, fp, a, b, modulus);
            let inner = d
                .kernel()
                .lam(anon, spec_ty, modulus, crate::BinderInfo::Default);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.hd_rec, vec![one]);
        let body = d.apply(rec, &[f, fp, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_hd, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
            d.lam_fv(f_fv, func_ty, with_fp)
        };
        let ty = {
            let with_u = d.arrow(carrier_hd, nat_fn);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
            d.pi_fv(f_fv, func_ty, with_fp)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.hd_modulus,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 45),
        })?;
    }

    // spec : ∀ F F' a b (u : HasDerivativeOn F F' a b),
    //   deriv_spec_body F F' a b (HasDerivativeOn.modulus F F' a b u)
    //   := fun F F' a b u => HasDerivativeOn.rec F F' a b
    //        (fun w => deriv_spec_body F F' a b (HasDerivativeOn.modulus F F' a b w))
    //        (fun modulus spec => spec) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_hd = hd_ty(d, p, f, fp, a, b);

        let claim = |d: &mut IntDev<'_>, w: ExprId| {
            let mod_of_w = d.const_app(p.hd_modulus, &[f, fp, a, b, w]);
            deriv_spec_body(d, p, f, fp, a, b, mod_of_w)
        };

        let motive = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let body = claim(d, w);
            d.lam_fv(w_fv, carrier_hd, body)
        };
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = deriv_spec_body(d, p, f, fp, a, b, modulus);
            let spec_fv = d.fresh_fvar();
            let spec_var = d.kernel().fvar(spec_fv);
            let inner = d.lam_fv(spec_fv, spec_ty, spec_var);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.hd_rec, vec![zero_level]);
        let body = d.apply(rec, &[f, fp, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_hd, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
            d.lam_fv(f_fv, func_ty, with_fp)
        };
        let ty = {
            let inner = claim(d, u);
            let with_u = d.pi_fv(u_fv, carrier_hd, inner);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
            d.pi_fv(f_fv, func_ty, with_fp)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.hd_spec,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// --- witness: `const` -----------------------------------------------------------

/// `Equiv (add (add c (neg c)) (neg (mul zero diff))) zero` — the error term
/// of the constant witness is `Equiv`-zero unconditionally: `mul zero diff ~
/// zero` ([`CRealPrelude::mul_comm`] then [`CRealPrelude::mul_zero`]), and
/// `add c (neg c) ~ zero` ([`CRealPrelude::add_neg`]).
fn const_error_equiv_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    diff_yx: ExprId,
) -> (ExprId, ExprId) {
    let zero_c = czero(d, p);
    let add_c_negc = cdiff(d, p, c, c);
    let mul_zero_diff = cmul(d, p, zero_c, diff_yx);
    let neg_mzd = cneg(d, p, mul_zero_diff);
    let error = cadd(d, p, add_c_negc, neg_mzd);

    // mul zero diff ~ zero, via mul_comm then mul_zero.
    let diff_zero = cmul(d, p, diff_yx, zero_c);
    let comm1 = d.lemma(p.mul_comm, &[zero_c, diff_yx]); // mul_zero_diff ~ diff_zero
    let mz = d.lemma(p.mul_zero, &[diff_yx]); // diff_zero ~ zero_c
    let mzd_equiv_zero = echain(d, p, mul_zero_diff, &[(diff_zero, comm1), (zero_c, mz)]);

    // neg(mul zero diff) ~ neg zero ~ zero.
    let neg_zero_c = cneg(d, p, zero_c);
    let step_neg = d.lemma(p.neg_congr, &[mul_zero_diff, zero_c, mzd_equiv_zero]);
    let nz_eq = neg_zero_equiv(d, p);
    let neg_mzd_equiv_zero = echain(d, p, neg_mzd, &[(neg_zero_c, step_neg), (zero_c, nz_eq)]);

    // add_c_negc ~ zero.
    let h1 = d.lemma(p.add_neg, &[c]);

    // error = add(add_c_negc, neg_mzd) ~ add(add_c_negc, zero) ~ add(zero,zero) ~ zero.
    let refl_addcnegc = d.lemma(p.equiv_refl, &[add_c_negc]);
    let s1_target = cadd(d, p, add_c_negc, zero_c);
    let s1_proof = d.lemma(
        p.add_congr,
        &[
            add_c_negc,
            add_c_negc,
            neg_mzd,
            zero_c,
            refl_addcnegc,
            neg_mzd_equiv_zero,
        ],
    );

    let s2_target = cadd(d, p, zero_c, zero_c);
    let refl_zero = d.lemma(p.equiv_refl, &[zero_c]);
    let s2_proof = d.lemma(
        p.add_congr,
        &[add_c_negc, zero_c, zero_c, zero_c, h1, refl_zero],
    );

    let s3_proof = d.lemma(p.add_zero, &[zero_c]);

    let proof = echain(
        d,
        p,
        error,
        &[
            (s1_target, s1_proof),
            (s2_target, s2_proof),
            (zero_c, s3_proof),
        ],
    );
    (error, proof)
}

/// `CReal.hasDerivative_const : ∀ c a b, HasDerivativeOn (fun _ => c) (fun _
/// => zero) a b`.
///
/// The cheapest witness: the error term is `c - c - 0*(y-x)`, `Equiv`-zero
/// regardless of the hypothesis, so any modulus works (`fun _ => 0` is
/// used) — mirroring
/// [`super::uniform_continuity::declare_uniformly_continuous_const`].
fn declare_has_derivative_const(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let const_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, c)
    };
    let zero_c = czero(d, p);
    let zero_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, zero_c)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let z = d.num(0);
        d.lam_fv(ignore_fv, nat, z)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
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

        let diff_yx = cdiff(d, p, y, x);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);

        let (error, error_equiv_zero) = const_error_equiv_zero(d, p, c, diff_yx);
        let (bound, bound_nonneg) = error_bound(d, p, e, diff_yx);
        let conclusion = close_zero_error(d, p, error, bound, error_equiv_zero, bound_nonneg);

        let h = d.kernel().fvar(h_fv);
        let _ = h;
        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[const_fn, zero_fn, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(c_fv, carrier, with_a)
    };
    let ty = {
        let applied = hd_ty(d, p, const_fn, zero_fn, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(c_fv, carrier, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_const,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `id` --------------------------------------------------------------

/// `Equiv (add diff (neg (mul one diff))) zero` — the error term of the
/// identity witness is `Equiv`-zero unconditionally: `mul one diff ~ diff`
/// ([`CRealPrelude::mul_comm`] then [`CRealPrelude::mul_one`]), so `diff -
/// 1*diff ~ diff - diff ~ zero` ([`CRealPrelude::add_neg`]).
fn id_error_equiv_zero(d: &mut IntDev<'_>, p: CRealPrelude, diff_yx: ExprId) -> (ExprId, ExprId) {
    let one_c = d.kernel().const_(p.one, vec![]);
    let mul_one_diff = cmul(d, p, one_c, diff_yx);
    let neg_mod = cneg(d, p, mul_one_diff);
    let error = cadd(d, p, diff_yx, neg_mod);

    let diff_one = cmul(d, p, diff_yx, one_c);
    let comm1 = d.lemma(p.mul_comm, &[one_c, diff_yx]); // mul_one_diff ~ diff_one
    let mo = d.lemma(p.mul_one, &[diff_yx]); // diff_one ~ diff_yx
    let mod_equiv_diff = echain(d, p, mul_one_diff, &[(diff_one, comm1), (diff_yx, mo)]);

    let neg_diff = cneg(d, p, diff_yx);
    let step_neg = d.lemma(p.neg_congr, &[mul_one_diff, diff_yx, mod_equiv_diff]); // neg_mod ~ neg_diff

    let refl_diff = d.lemma(p.equiv_refl, &[diff_yx]);
    let s1_target = cadd(d, p, diff_yx, neg_diff);
    let s1_proof = d.lemma(
        p.add_congr,
        &[diff_yx, diff_yx, neg_mod, neg_diff, refl_diff, step_neg],
    );

    let zero_c = czero(d, p);
    let s2_proof = d.lemma(p.add_neg, &[diff_yx]); // s1_target ~ zero_c

    let proof = echain(d, p, error, &[(s1_target, s1_proof), (zero_c, s2_proof)]);
    (error, proof)
}

/// `CReal.hasDerivative_id : ∀ a b, HasDerivativeOn (fun r => r) (fun _ =>
/// one) a b`.
///
/// The error term is `(y-x) - 1*(y-x)`, `Equiv`-zero regardless of the
/// hypothesis, so any modulus works (`fun _ => 0` is used) — the same shape
/// as [`declare_has_derivative_const`], one law swapped (`mul_one` for
/// `mul_zero`).
fn declare_has_derivative_id(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let one_c = d.kernel().const_(p.one, vec![]);
    let one_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, one_c)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let z = d.num(0);
        d.lam_fv(ignore_fv, nat, z)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
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

        let diff_yx = cdiff(d, p, y, x);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);

        let (error, error_equiv_zero) = id_error_equiv_zero(d, p, diff_yx);
        let (bound, bound_nonneg) = error_bound(d, p, e, diff_yx);
        let conclusion = close_zero_error(d, p, error, bound, error_equiv_zero, bound_nonneg);

        let h = d.kernel().fvar(h_fv);
        let _ = h;
        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[identity, one_fn, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let applied = hd_ty(d, p, identity, one_fn, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_id,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `sq` -----------------------------------------------------------

/// The error term for `F := fun r => mul r r`, `F' := fun x => add x x` is
/// **exactly** `mul diff diff` (not merely `Equiv`-zero, unlike
/// `const`/`id`): `y*y - x*x - (x+x)*(y-x) = (y-x)*(y+x) - (x+x)*(y-x) =
/// (y-x)*(y-x)`, using [`diff_of_squares`] once for `y*y - x*x` and again
/// (through [`neg_add_distrib`]) to cancel `(y+x) - (x+x)` down to `y - x`.
/// Returns `(error, diff, proof : Equiv error (mul diff diff))`.
fn sq_error_equiv_diffsq(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let nx = cneg(d, p, x);
    let diff = cadd(d, p, y, nx); // y - x
    let sumyx = cadd(d, p, y, x); // y + x
    let sumxx = cadd(d, p, x, x); // x + x
    let fy = cmul(d, p, y, y);
    let fx = cmul(d, p, x, x);
    let neg_fx = cneg(d, p, fx);
    let fy_fx = cadd(d, p, fy, neg_fx);
    let deriv_term = cmul(d, p, sumxx, diff);
    let neg_deriv_term = cneg(d, p, deriv_term);
    let error = cadd(d, p, fy_fx, neg_deriv_term);
    let sqdiff = cmul(d, p, diff, diff);

    // Step A: fy_fx ~ mul diff sumyx, via `diff_of_squares(y, x)`.
    let mul_diff_sumyx = cmul(d, p, diff, sumyx);
    let dos_yx = diff_of_squares(d, p, y, x); // Equiv mul_diff_sumyx fy_fx
    let step_a = esymm(d, p, mul_diff_sumyx, fy_fx, dos_yx); // Equiv fy_fx mul_diff_sumyx

    let step1_target = cadd(d, p, mul_diff_sumyx, neg_deriv_term);
    let refl_negderiv = erefl(d, p, neg_deriv_term);
    let step_a_congr = d.lemma(
        p.add_congr,
        &[
            fy_fx,
            mul_diff_sumyx,
            neg_deriv_term,
            neg_deriv_term,
            step_a,
            refl_negderiv,
        ],
    ); // Equiv error step1_target

    // Step B: neg deriv_term ~ neg (mul diff sumxx), via mul_comm.
    let mul_diff_sumxx = cmul(d, p, diff, sumxx);
    let mc = d.lemma(p.mul_comm, &[sumxx, diff]); // Equiv deriv_term mul_diff_sumxx
    let neg_mul_diff_sumxx = cneg(d, p, mul_diff_sumxx);
    let neg_mc = d.lemma(p.neg_congr, &[deriv_term, mul_diff_sumxx, mc]);

    let step2_target = cadd(d, p, mul_diff_sumyx, neg_mul_diff_sumxx);
    let refl_muldiffsumyx = erefl(d, p, mul_diff_sumyx);
    let step_b_congr = d.lemma(
        p.add_congr,
        &[
            mul_diff_sumyx,
            mul_diff_sumyx,
            neg_deriv_term,
            neg_mul_diff_sumxx,
            refl_muldiffsumyx,
            neg_mc,
        ],
    ); // Equiv step1_target step2_target

    // Step C: step2_target ~ mul diff (sumyx - sumxx), via left_distrib and
    // `mul_neg_equiv`.
    let neg_sumxx = cneg(d, p, sumxx);
    let mul_diff_negsumxx = cmul(d, p, diff, neg_sumxx);
    let mne = mul_neg_equiv(d, p, diff, sumxx); // Equiv mul_diff_negsumxx neg_mul_diff_sumxx

    let sum_yx_negsumxx = cadd(d, p, sumyx, neg_sumxx);
    let mul_diff_sum = cmul(d, p, diff, sum_yx_negsumxx);
    let ld = d.lemma(p.left_distrib, &[diff, sumyx, neg_sumxx]);
    let ld_target = cadd(d, p, mul_diff_sumyx, mul_diff_negsumxx);
    let refl_muldiffsumyx2 = erefl(d, p, mul_diff_sumyx);
    let ld_congr = d.lemma(
        p.add_congr,
        &[
            mul_diff_sumyx,
            mul_diff_sumyx,
            mul_diff_negsumxx,
            neg_mul_diff_sumxx,
            refl_muldiffsumyx2,
            mne,
        ],
    ); // Equiv ld_target step2_target

    let ld_combined = echain(
        d,
        p,
        mul_diff_sum,
        &[(ld_target, ld), (step2_target, ld_congr)],
    );
    let step_c = esymm(d, p, mul_diff_sum, step2_target, ld_combined); // Equiv step2_target mul_diff_sum

    // Step D: sum_yx_negsumxx ~ diff (the cancellation).
    let nx_nx = cadd(d, p, nx, nx);
    let nad = neg_add_distrib(d, p, x, x); // Equiv neg_sumxx nx_nx
    let refl_sumyx = erefl(d, p, sumyx);
    let sum_yx_nxnx = cadd(d, p, sumyx, nx_nx);
    let step_c1 = d.lemma(
        p.add_congr,
        &[sumyx, sumyx, neg_sumxx, nx_nx, refl_sumyx, nad],
    ); // Equiv sum_yx_negsumxx sum_yx_nxnx

    let x_nxnx = cadd(d, p, x, nx_nx);
    let y_x_nxnx = cadd(d, p, y, x_nxnx);
    let e1 = d.lemma(p.add_assoc, &[y, x, nx_nx]); // Equiv sum_yx_nxnx y_x_nxnx

    let x_nx = cadd(d, p, x, nx);
    let xnx_nx = cadd(d, p, x_nx, nx);
    let e2 = d.lemma(p.add_assoc, &[x, nx, nx]); // Equiv xnx_nx x_nxnx
    let e2_symm = esymm(d, p, xnx_nx, x_nxnx, e2); // Equiv x_nxnx xnx_nx

    let refl_y = erefl(d, p, y);
    let y_xnxnx = cadd(d, p, y, xnx_nx);
    let e2c = d.lemma(p.add_congr, &[y, y, x_nxnx, xnx_nx, refl_y, e2_symm]); // Equiv y_x_nxnx y_xnxnx

    let zero_c = czero(d, p);
    let e3 = d.lemma(p.add_neg, &[x]); // Equiv x_nx zero_c
    let refl_nx = erefl(d, p, nx);
    let zero_nx = cadd(d, p, zero_c, nx);
    let e3c = d.lemma(p.add_congr, &[x_nx, zero_c, nx, nx, e3, refl_nx]); // Equiv xnx_nx zero_nx

    let refl_y2 = erefl(d, p, y);
    let y_zeronx = cadd(d, p, y, zero_nx);
    let e3cc = d.lemma(p.add_congr, &[y, y, xnx_nx, zero_nx, refl_y2, e3c]); // Equiv y_xnxnx y_zeronx

    let nx_zero = cadd(d, p, nx, zero_c);
    let e4 = d.lemma(p.add_comm, &[zero_c, nx]); // Equiv zero_nx nx_zero
    let e5 = d.lemma(p.add_zero, &[nx]); // Equiv nx_zero nx
    let e45 = echain(d, p, zero_nx, &[(nx_zero, e4), (nx, e5)]); // Equiv zero_nx nx

    let refl_y3 = erefl(d, p, y);
    let e45c = d.lemma(p.add_congr, &[y, y, zero_nx, nx, refl_y3, e45]); // Equiv y_zeronx diff

    let final_regroup = echain(
        d,
        p,
        sum_yx_nxnx,
        &[
            (y_x_nxnx, e1),
            (y_xnxnx, e2c),
            (y_zeronx, e3cc),
            (diff, e45c),
        ],
    ); // Equiv sum_yx_nxnx diff

    let cancel_d = echain(
        d,
        p,
        sum_yx_negsumxx,
        &[(sum_yx_nxnx, step_c1), (diff, final_regroup)],
    ); // Equiv sum_yx_negsumxx diff

    let refl_diff = erefl(d, p, diff);
    let mul_congr_result = d.lemma(
        p.mul_congr,
        &[diff, diff, sum_yx_negsumxx, diff, refl_diff, cancel_d],
    ); // Equiv mul_diff_sum sqdiff

    let final_proof = echain(
        d,
        p,
        error,
        &[
            (step1_target, step_a_congr),
            (step2_target, step_b_congr),
            (mul_diff_sum, step_c),
            (sqdiff, mul_congr_result),
        ],
    );

    (error, diff, final_proof)
}

/// `CReal.hasDerivative_sq : ∀ a b, HasDerivativeOn (fun r => mul r r) (fun x
/// => add x x) a b`.
///
/// The first nonlinear derivative in this kernel. The error term is
/// **exactly** `(y-x)*(y-x)` ([`sq_error_equiv_diffsq`]), not merely
/// `Equiv`-zero, so the modulus is the identity (`fun n => n`, mirroring `id`)
/// and the bound closes via [`sq_le_abs_sq`] plus
/// [`CRealPrelude::mul_le_mul_of_nonneg_left`]: `|y-x|^2 <= |y-x| *
/// (1/(e+1))`.
fn declare_has_derivative_sq(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let square = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let rr = cmul(d, p, r, r);
        d.lam_fv(r_fv, carrier, rr)
    };
    let double = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let xx = cadd(d, p, x, x);
        d.lam_fv(x_fv, carrier, xx)
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
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
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

        let (error, diff, error_equiv_sqdiff) = sq_error_equiv_diffsq(d, p, x, y);
        let abs_diff = cabs(d, p, diff);
        let abs_diff_nonneg = d.lemma(p.abs_nonneg, &[diff]);

        let mod_e = d.apply(modulus, &[e]);
        let (q, q_nonneg) = nonneg_rat_bound(d, p, 1, mod_e);
        let hyp = within_real(d, p, diff, q);
        let h = d.kernel().fvar(h_fv);

        let bound = cmul(d, p, q, abs_diff);
        let bound_nonneg = d.lemma(p.mul_nonneg, &[q, abs_diff, q_nonneg, abs_diff_nonneg]);

        let sqdiff = cmul(d, p, diff, diff);
        let sq_bound_step = sq_le_abs_sq(d, p, diff); // le sqdiff (mul abs_diff abs_diff)
        let mul_abs_abs = cmul(d, p, abs_diff, abs_diff);
        let mul_abs_q = cmul(d, p, abs_diff, q);
        let mlm = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[abs_diff, abs_diff, q, abs_diff_nonneg, h],
        ); // le mul_abs_abs mul_abs_q
        let step_ab = d.lemma(
            p.le_trans,
            &[sqdiff, mul_abs_abs, mul_abs_q, sq_bound_step, mlm],
        ); // le sqdiff mul_abs_q
        let comm_qa = d.lemma(p.mul_comm, &[abs_diff, q]); // Equiv mul_abs_q bound
        let refl_sqdiff = erefl(d, p, sqdiff);
        let h_upper_sqdiff = d.lemma(
            p.le_congr,
            &[
                sqdiff,
                sqdiff,
                mul_abs_q,
                bound,
                refl_sqdiff,
                comm_qa,
                step_ab,
            ],
        ); // le sqdiff bound

        let sqn = d.lemma(p.sq_nonneg, &[diff]); // le zero sqdiff
        let h_lower_sqdiff = neg_le_of_nonneg(d, p, sqdiff, bound, sqn, bound_nonneg); // le (neg sqdiff) bound

        let error_equiv_sqdiff_symm = esymm(d, p, error, sqdiff, error_equiv_sqdiff); // Equiv sqdiff error
        let refl_bound = erefl(d, p, bound);
        let h_upper_error = d.lemma(
            p.le_congr,
            &[
                sqdiff,
                error,
                bound,
                bound,
                error_equiv_sqdiff_symm,
                refl_bound,
                h_upper_sqdiff,
            ],
        ); // le error bound

        let neg_sqdiff = cneg(d, p, sqdiff);
        let neg_error = cneg(d, p, error);
        let neg_eq = d.lemma(p.neg_congr, &[sqdiff, error, error_equiv_sqdiff_symm]);
        let h_lower_error = d.lemma(
            p.le_congr,
            &[
                neg_sqdiff,
                neg_error,
                bound,
                bound,
                neg_eq,
                refl_bound,
                h_lower_sqdiff,
            ],
        ); // le (neg error) bound

        let conclusion = d.lemma(p.abs_le, &[error, bound, h_upper_error, h_lower_error]);

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[square, double, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let applied = hd_ty(d, p, square, double, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_sq,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `neg` -----------------------------------------------------------

/// `CReal.hasDerivative_neg : ∀ F F' a b, HasDerivativeOn F F' a b →
/// HasDerivativeOn (fun r => neg (F r)) (fun x => neg (F' x)) a b`.
///
/// `neg`'s scaling factor is exactly `-1`, so — unlike the sum rule below —
/// it needs no rescaled modulus at all: `neg`'s error term at accuracy `e` is
/// **exactly** `neg` of `F`'s own error term at the SAME `e`
/// ([`neg_error_equiv_neg`]), so `F`'s own hypothesis at `e` is already
/// exactly what `F`'s own spec needs, and [`le_abs_neg_of_le_abs`] turns
/// `F`'s own bound into the bound `neg`'s error needs, transported along that
/// `Equiv` by [`abs_le_of_equiv`].
fn declare_has_derivative_neg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let neg_f = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let nfr = cneg(d, p, fr);
        d.lam_fv(r_fv, carrier, nfr)
    };
    let neg_fp = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let nfpx = cneg(d, p, fpx);
        d.lam_fv(x_fv, carrier, nfpx)
    };
    // Reuse F's own modulus verbatim: `neg`'s error is exactly `neg` of F's,
    // so no rescaling is needed.
    let modulus = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
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

        let diff_yx = cdiff(d, p, y, x);
        let abs_diff = cabs(d, p, diff_yx);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);
        let h_fv_expr = d.kernel().fvar(h_fv);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let deriv_term_f = cmul(d, p, fpx, diff_yx);
        let fy_fx_f = cdiff(d, p, fy, fx);
        let error_f = cdiff(d, p, fy_fx_f, deriv_term_f);

        let neg_fy = cneg(d, p, fy);
        let neg_fx = cneg(d, p, fx);
        let neg_neg_fx = cneg(d, p, neg_fx);
        let neg_fpx = cneg(d, p, fpx);
        let fy_fx_neg = cadd(d, p, neg_fy, neg_neg_fx);
        let deriv_term_neg = cmul(d, p, neg_fpx, diff_yx);
        let neg_deriv_term_neg = cneg(d, p, deriv_term_neg);
        let error_neg = cadd(d, p, fy_fx_neg, neg_deriv_term_neg);

        let out_bound_rat = div_succ(d, p, 1, e);
        let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);
        let out_bound = cmul(d, p, ofr_out, abs_diff);

        // Step 1: `neg error_f ~ add(add(neg fy, neg(neg fx)), mul fpx diff)`.
        // `error_f = add(fy_fx_f, neg(deriv_term_f))` (a DIFFERENCE, not a
        // sum), so the outer split is over `(fy_fx_f, neg_deriv_term_f)`,
        // and the second component needs `double_neg` to fold the resulting
        // `neg(neg(deriv_term_f))` back to `deriv_term_f`.
        let neg_p_step = neg_add_distrib(d, p, fy, neg_fx); // neg(fy-fx) ~ (-fy)+(-(-fx))
        let neg_q_step = double_neg(d, p, deriv_term_f); // -(-(mul fpx diff)) ~ mul fpx diff
        let rhs_target = cadd(d, p, fy_fx_neg, deriv_term_f);
        let neg_error_f = cneg(d, p, error_f);
        let neg_deriv_term_f = cneg(d, p, deriv_term_f);
        let neg_fy_fx_f = cneg(d, p, fy_fx_f);
        let neg_error_f_split = neg_add_distrib(d, p, fy_fx_f, neg_deriv_term_f); // -error_f ~ (-fy_fx_f)+(-(-deriv_term_f))
        let neg_neg_deriv_term_f = cneg(d, p, neg_deriv_term_f);
        let step1_congr = d.lemma(
            p.add_congr,
            &[
                neg_fy_fx_f,
                fy_fx_neg,
                neg_neg_deriv_term_f,
                deriv_term_f,
                neg_p_step,
                neg_q_step,
            ],
        );
        let neg_error_f_split_target = cadd(d, p, neg_fy_fx_f, neg_neg_deriv_term_f);
        let neg_error_f_to_rhs = echain(
            d,
            p,
            neg_error_f,
            &[
                (neg_error_f_split_target, neg_error_f_split),
                (rhs_target, step1_congr),
            ],
        );

        // Step 2: `error_neg ~ rhs_target` (first component is syntactically
        // identical; second needs `neg(mul(neg fpx, diff)) ~ mul fpx diff`).
        let nmel = neg_mul_equiv_left(d, p, fpx, diff_yx); // mul(neg fpx, diff) ~ neg(mul fpx diff)
        let neg_congr_nmel = d.lemma(p.neg_congr, &[deriv_term_neg, neg_deriv_term_f, nmel]);
        let dn2 = double_neg(d, p, deriv_term_f); // neg(neg(mul fpx diff)) ~ mul fpx diff
        let second_component = echain(
            d,
            p,
            neg_deriv_term_neg,
            &[(neg_neg_deriv_term_f, neg_congr_nmel), (deriv_term_f, dn2)],
        );
        let refl_fst = erefl(d, p, fy_fx_neg);
        let error_neg_to_rhs = d.lemma(
            p.add_congr,
            &[
                fy_fx_neg,
                fy_fx_neg,
                neg_deriv_term_neg,
                deriv_term_f,
                refl_fst,
                second_component,
            ],
        );

        // Step 3: combine.
        let rhs_to_neg_error_f = esymm(d, p, neg_error_f, rhs_target, neg_error_f_to_rhs);
        let error_neg_equiv_neg_error_f = echain(
            d,
            p,
            error_neg,
            &[
                (rhs_target, error_neg_to_rhs),
                (neg_error_f, rhs_to_neg_error_f),
            ],
        );

        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);
        let error_f_bound = d.lemma(
            p.hd_spec,
            &[f, fp, a, b, hf, e, x, y, hax, hxb, hay, hyb, h_fv_expr],
        ); // le (abs error_f) out_bound
        let neg_error_f_bound = le_abs_neg_of_le_abs(d, p, error_f, out_bound, error_f_bound);
        let conclusion = abs_le_of_equiv(
            d,
            p,
            error_neg,
            neg_error_f,
            out_bound,
            error_neg_equiv_neg_error_f,
            neg_error_f_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[neg_f, neg_fp, a, b, modulus, spec]);
    let value = {
        let with_hf = d.lam_fv(hf_fv, hf_ty, mk_applied);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, neg_f, neg_fp, a, b);
        let with_hf = d.arrow(hf_ty, applied);
        let with_b = d.pi_fv(b_fv, carrier, with_hf);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_neg,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `add` (the sum rule) --------------------------------------------

/// `CReal.hasDerivative_add : ∀ F F' G G' a b, HasDerivativeOn F F' a b →
/// HasDerivativeOn G G' a b → HasDerivativeOn (fun r => add (F r) (G r))
/// (fun x => add (F' x) (G' x)) a b`.
///
/// **The sum rule**, unblocked by [`RatPrelude::nat_div_succ_antitone`]
/// (see the module documentation). The combined modulus at accuracy `e` is
/// `mF (2e+1) + mG (2e+1)` (`Nat.add`, not `max` — `nat_prelude` has no
/// `Nat.max`, and `Nat.le_add_right`/`Nat.add_comm` give both `<=`
/// directions just as well: `mF(2e+1) <= mF(2e+1)+mG(2e+1)` directly, and
/// `mG(2e+1) <= mG(2e+1)+mF(2e+1) = mF(2e+1)+mG(2e+1)` after one
/// commutation). Antitonicity reads the hypothesis at the combined modulus
/// back down to each sub-derivative's own hypothesis at `2e+1`;
/// `F`'s/`G`'s own specs at `2e+1` each bound their error by `1/(2e+2) ·
/// |y-x|`; and `Rat.natDivSucc_add` + `Rat.natDivSucc_halve` fuse the two
/// `1/(2e+2)` bounds into the single target `1/(e+1)` (`1/(2e+2) +
/// 1/(2e+2) = 2/(2e+2) = 1/(e+1)`). The combined error term itself needs a
/// six-term commutative/associative regroup ([`add4_comm`], applied twice)
/// plus [`neg_add_distrib`]/[`right_distrib`] to see that it IS `F`'s error
/// plus `G`'s error, exactly.
fn declare_has_derivative_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let gp_fv = d.fresh_fvar();
    let gp = d.kernel().fvar(gp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = hd_ty(d, p, g, gp, a, b);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let fsum = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let sum = cadd(d, p, fr, gr);
        d.lam_fv(r_fv, carrier, sum)
    };
    let fsum_p = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let gpx = d.apply(gp, &[x]);
        let sum = cadd(d, p, fpx, gpx);
        d.lam_fv(x_fv, carrier, sum)
    };
    let mf = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);
    let mg = d.const_app(p.hd_modulus, &[g, gp, a, b, hg]);
    // `modulus_sum e := mF (2e+1) + mG (2e+1)`.
    let modulus_sum = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let two = d.num(2);
        let two_e = d.mul(two, e);
        let e_prime = d.succ(two_e);
        let mf_e2 = d.apply(mf, &[e_prime]);
        let mg_e2 = d.apply(mg, &[e_prime]);
        let sum = d.add(mf_e2, mg_e2);
        d.lam_fv(e_fv, nat, sum)
    };

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
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

        let diff_yx = cdiff(d, p, y, x);
        let abs_diff = cabs(d, p, diff_yx);

        let mod_e = d.apply(modulus_sum, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);
        let h = d.kernel().fvar(h_fv);

        // --- the index/modulus arithmetic ------------------------------------
        let two = d.num(2);
        let two_e = d.mul(two, e);
        let e_prime = d.succ(two_e);
        let mf_e2 = d.apply(mf, &[e_prime]);
        let mg_e2 = d.apply(mg, &[e_prime]);
        let modulus_sum_e = d.add(mf_e2, mg_e2);
        let mg_plus_mf = d.add(mg_e2, mf_e2);

        let nat_p = p.rat.int.nat;
        let h_le_f = d.lemma(nat_p.le_add_right, &[mf_e2, mg_e2]); // Le mf_e2 (add mf_e2 mg_e2)
        let raw_g = d.lemma(nat_p.le_add_right, &[mg_e2, mf_e2]); // Le mg_e2 (add mg_e2 mf_e2)
        let comm_eq = d.lemma(nat_p.add_comm, &[mg_e2, mf_e2]); // Eq (add mg_e2 mf_e2) (add mf_e2 mg_e2)
        let h_le_g = nat_rewrite_prop(d, mg_plus_mf, modulus_sum_e, comm_eq, raw_g, &|d, t| {
            d.le(mg_e2, t)
        });

        let r_f = div_succ(d, p, 1, mf_e2);
        let r_g = div_succ(d, p, 1, mg_e2);
        let r_sum = div_succ(d, p, 1, modulus_sum_e);
        let rat_f = d.lemma(p.rat.nat_div_succ_antitone, &[mf_e2, modulus_sum_e, h_le_f]); // Rat.le r_sum r_f
        let rat_g = d.lemma(p.rat.nat_div_succ_antitone, &[mg_e2, modulus_sum_e, h_le_g]); // Rat.le r_sum r_g

        let ofr_sum = d.const_app(p.of_rat, &[r_sum]);
        let ofr_f = d.const_app(p.of_rat, &[r_f]);
        let ofr_g = d.const_app(p.of_rat, &[r_g]);
        let creal_f = d.lemma(p.of_rat_le, &[r_sum, r_f, rat_f]); // le ofr_sum ofr_f
        let creal_g = d.lemma(p.of_rat_le, &[r_sum, r_g, rat_g]); // le ofr_sum ofr_g

        let hyp_f = d.lemma(p.le_trans, &[abs_diff, ofr_sum, ofr_f, h, creal_f]); // le abs_diff ofr_f
        let hyp_g = d.lemma(p.le_trans, &[abs_diff, ofr_sum, ofr_g, h, creal_g]); // le abs_diff ofr_g

        // --- F's and G's own error terms and bounds, at accuracy `2e+1` -----
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);
        let gpx = d.apply(gp, &[x]);

        let mfxd = cmul(d, p, fpx, diff_yx);
        let mgxd = cmul(d, p, gpx, diff_yx);
        let fy_fx_f = cdiff(d, p, fy, fx);
        let fy_fx_g = cdiff(d, p, gy, gx);
        let error_f = cdiff(d, p, fy_fx_f, mfxd);
        let error_g = cdiff(d, p, fy_fx_g, mgxd);

        let error_f_bound = d.lemma(
            p.hd_spec,
            &[f, fp, a, b, hf, e_prime, x, y, hax, hxb, hay, hyb, hyp_f],
        ); // le (abs error_f) (mul (ofRat r_prime') abs_diff)
        let error_g_bound = d.lemma(
            p.hd_spec,
            &[g, gp, a, b, hg, e_prime, x, y, hax, hxb, hay, hyb, hyp_g],
        );

        let r_prime = div_succ(d, p, 1, e_prime);
        let q_prime = d.const_app(p.of_rat, &[r_prime]);
        let q_bound = cmul(d, p, q_prime, abs_diff);

        // --- combine the two bounds via the triangle inequality -------------
        let combined_error = cadd(d, p, error_f, error_g);
        let abs_error_f = cabs(d, p, error_f);
        let abs_error_g = cabs(d, p, error_g);
        let triangle = abs_add_le(d, p, error_f, error_g); // le (abs combined_error) (add abs_error_f abs_error_g)
        let sum_bounds = d.lemma(
            p.add_le_add,
            &[
                abs_error_f,
                q_bound,
                abs_error_g,
                q_bound,
                error_f_bound,
                error_g_bound,
            ],
        ); // le (add abs_error_f abs_error_g) (add q_bound q_bound)
        let abs_combined_error = cabs(d, p, combined_error);
        let abs_error_f_plus_g = cadd(d, p, abs_error_f, abs_error_g);
        let q_bound_plus_q_bound = cadd(d, p, q_bound, q_bound);
        let combined_le = d.lemma(
            p.le_trans,
            &[
                abs_combined_error,
                abs_error_f_plus_g,
                q_bound_plus_q_bound,
                triangle,
                sum_bounds,
            ],
        ); // le (abs combined_error) (add q_bound q_bound)

        // --- fuse `add q_bound q_bound` down to the single target bound -----
        let out_bound_rat = div_succ(d, p, 1, e);
        let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);
        let out_bound = cmul(d, p, ofr_out, abs_diff);

        let one_nat = d.num(1);
        let of_rat_add_proof = d.lemma(p.of_rat_add, &[r_prime, r_prime]); // Equiv (add q_prime q_prime) (ofRat (Rat.add r_prime r_prime))
        let eq1 = d.lemma(p.rat.nat_div_succ_add, &[one_nat, one_nat, e_prime]); // Eq (Rat.add r_prime r_prime) (natDivSucc (add 1 1) e_prime)
        let two_e_prime = div_succ(d, p, 2, e_prime);
        let radd_r_prime_r_prime = radd(d, r_prime, r_prime);
        let q_prime_plus_q_prime = cadd(d, p, q_prime, q_prime);
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
        ); // Equiv (add q_prime q_prime) (ofRat two_e_prime)
        let eq2 = d.lemma(p.rat.nat_div_succ_halve, &[e]); // Eq two_e_prime (natDivSucc 1 e)
        let sum_equiv_target_rat =
            rat_eq_rewrite(d, two_e_prime, out_bound_rat, eq2, step_a, &|d, t| {
                let oft = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[q_prime_plus_q_prime, oft])
            }); // Equiv (add q_prime q_prime) ofr_out

        let mul_q_prime_sum_abs_diff = cmul(d, p, q_prime_plus_q_prime, abs_diff);
        let rd = right_distrib(d, p, q_prime, q_prime, abs_diff); // Equiv (mul (add q_prime q_prime) abs_diff) (add q_bound q_bound)
        let rd_symm = esymm(d, p, mul_q_prime_sum_abs_diff, q_bound_plus_q_bound, rd); // Equiv (add q_bound q_bound) (mul (add q_prime q_prime) abs_diff)
        let refl_abs_diff = erefl(d, p, abs_diff);
        let mul_step = d.lemma(
            p.mul_congr,
            &[
                q_prime_plus_q_prime,
                ofr_out,
                abs_diff,
                abs_diff,
                sum_equiv_target_rat,
                refl_abs_diff,
            ],
        ); // Equiv (mul (add q_prime q_prime) abs_diff) out_bound
        let bound_equiv = echain(
            d,
            p,
            q_bound_plus_q_bound,
            &[(mul_q_prime_sum_abs_diff, rd_symm), (out_bound, mul_step)],
        ); // Equiv (add q_bound q_bound) out_bound

        let combined_error_bound = {
            let abs_combined = cabs(d, p, combined_error);
            let refl_abs = erefl(d, p, abs_combined);
            d.lemma(
                p.le_congr,
                &[
                    abs_combined,
                    abs_combined,
                    q_bound_plus_q_bound,
                    out_bound,
                    refl_abs,
                    bound_equiv,
                    combined_le,
                ],
            )
        }; // le (abs combined_error) out_bound

        // --- the actual error term IS F's error plus G's, exactly -----------
        let fsum_y = d.apply(fsum, &[y]);
        let fsum_x = d.apply(fsum, &[x]);
        let fsum_p_x = d.apply(fsum_p, &[x]);
        let deriv_term_sum = cmul(d, p, fsum_p_x, diff_yx);
        let fy_fx_sum = cdiff(d, p, fsum_y, fsum_x);
        let actual_error = cdiff(d, p, fy_fx_sum, deriv_term_sum);

        let neg_fx = cneg(d, p, fx);
        let neg_gx = cneg(d, p, gx);
        let neg_mfxd = cneg(d, p, mfxd);
        let neg_mgxd = cneg(d, p, mgxd);

        // Step A: `neg (add fx gx) ~ add (neg fx) (neg gx)`.
        let step_a_eq = neg_add_distrib(d, p, fx, gx);
        // Step B: `neg (mul (add fpx gpx) diff) ~ add (neg mfxd) (neg mgxd)`.
        let fpx_plus_gpx = cadd(d, p, fpx, gpx);
        let rd_fg = right_distrib(d, p, fpx, gpx, diff_yx); // Equiv (mul (add fpx gpx) diff) (add mfxd mgxd)
        let deriv_sum_raw = cmul(d, p, fpx_plus_gpx, diff_yx);
        let mfxd_plus_mgxd = cadd(d, p, mfxd, mgxd);
        let neg_congr_rdfg = d.lemma(p.neg_congr, &[deriv_sum_raw, mfxd_plus_mgxd, rd_fg]); // Equiv (neg deriv_sum_raw) (neg (add mfxd mgxd))
        let step_b_split = neg_add_distrib(d, p, mfxd, mgxd); // Equiv (neg (add mfxd mgxd)) (add (neg mfxd) (neg mgxd))
        let neg_deriv_sum_raw = cneg(d, p, deriv_sum_raw);
        let neg_mfxd_plus_mgxd = cneg(d, p, mfxd_plus_mgxd);
        let neg_mfxd_neg_mgxd = cadd(d, p, neg_mfxd, neg_mgxd);
        let step_b_eq = echain(
            d,
            p,
            neg_deriv_sum_raw,
            &[
                (neg_mfxd_plus_mgxd, neg_congr_rdfg),
                (neg_mfxd_neg_mgxd, step_b_split),
            ],
        );

        // Step C: `actual_error ~ intermediate`.
        let p1 = cadd(d, p, fy, gy);
        let fx_plus_gx = cadd(d, p, fx, gx);
        let neg_fx_plus_gx = cneg(d, p, fx_plus_gx);
        let neg_fx_neg_gx = cadd(d, p, neg_fx, neg_gx);
        let refl_p1 = erefl(d, p, p1);
        let fst_lift = d.lemma(
            p.add_congr,
            &[p1, p1, neg_fx_plus_gx, neg_fx_neg_gx, refl_p1, step_a_eq],
        ); // Equiv fy_fx_sum (add p1 (add (neg fx) (neg gx)))
        let intermediate_fst = cadd(d, p, p1, neg_fx_neg_gx);
        let intermediate = cadd(d, p, intermediate_fst, neg_mfxd_neg_mgxd);
        let step_c_eq = d.lemma(
            p.add_congr,
            &[
                fy_fx_sum,
                intermediate_fst,
                neg_deriv_sum_raw,
                neg_mfxd_neg_mgxd,
                fst_lift,
                step_b_eq,
            ],
        ); // Equiv actual_error intermediate

        // Step D: `add4_comm` on the first four terms.
        let (target1, proof1) = add4_comm(d, p, fy, gy, neg_fx, neg_gx);
        // target1 = add (add fy (neg fx)) (add gy (neg gx))
        let refl_neg_mfxd_neg_mgxd = erefl(d, p, neg_mfxd_neg_mgxd);
        let intermediate2_congr = d.lemma(
            p.add_congr,
            &[
                intermediate_fst,
                target1,
                neg_mfxd_neg_mgxd,
                neg_mfxd_neg_mgxd,
                proof1,
                refl_neg_mfxd_neg_mgxd,
            ],
        ); // Equiv intermediate (add target1 (add neg_mfxd neg_mgxd))

        // Step E: `add4_comm` again, on `target1`'s two halves against the
        // negated derivative terms — lands exactly on `add error_f error_g`.
        let a0 = cadd(d, p, fy, neg_fx);
        let b0 = cadd(d, p, gy, neg_gx);
        let (target2, proof2) = add4_comm(d, p, a0, b0, neg_mfxd, neg_mgxd);
        // target2 = add (add a0 neg_mfxd) (add b0 neg_mgxd) = add error_f error_g

        let target1_plus_neg_mfxd_neg_mgxd = cadd(d, p, target1, neg_mfxd_neg_mgxd);
        let ring_chain = echain(
            d,
            p,
            actual_error,
            &[
                (intermediate, step_c_eq),
                (target1_plus_neg_mfxd_neg_mgxd, intermediate2_congr),
                (target2, proof2),
            ],
        ); // Equiv actual_error combined_error (target2 == combined_error, definitionally)

        let conclusion = abs_le_of_equiv(
            d,
            p,
            actual_error,
            combined_error,
            out_bound,
            ring_chain,
            combined_error_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[fsum, fsum_p, a, b, modulus_sum, spec]);
    let value = {
        let with_hg = d.lam_fv(hg_fv, hg_ty, mk_applied);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hg);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_gp = d.lam_fv(gp_fv, func_ty, with_a);
        let with_g = d.lam_fv(g_fv, func_ty, with_gp);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_g);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, fsum, fsum_p, a, b);
        let with_hg = d.arrow(hg_ty, applied);
        let with_hf = d.arrow(hf_ty, with_hg);
        let with_b = d.pi_fv(b_fv, carrier, with_hf);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_gp = d.pi_fv(gp_fv, func_ty, with_a);
        let with_g = d.pi_fv(g_fv, func_ty, with_gp);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_g);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_add,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `smul` (the scalar-multiple rule) -------------------------------

/// `CReal.hasDerivative_smul : ∀ (c : CReal) (F F' a b : CReal → CReal → …),
/// HasDerivativeOn F F' a b → ∀ (k : Nat), le (abs c) (ofRat (natDivSucc
/// (Nat.succ k) 0)) → HasDerivativeOn (fun r => mul c (F r)) (fun x => mul c
/// (F' x)) a b`. See [`CRealPrelude::has_derivative_smul`] and the module
/// documentation's "scalar-multiple rule" section for the route: reuse `F`'s
/// own modulus at the rescaled accuracy `e' := (k+1)·e + k` (no combination,
/// so no antitonicity), bound `|c·error_F|` via
/// [`declare_abs_mul_le_of_bounds`]'s `abs_mul_le_of_bounds`, then fold
/// `(k+1)·(1/(e'+1))` down to `1/(e+1)` via `Rat.natDivSucc_mul` +
/// `Nat.mul_one` + `Rat.natDivSucc_scale`.
fn declare_has_derivative_smul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // hbound : le (abs c) (ofRat (natDivSucc (Nat.succ k) 0))
    let zero_idx = d.num(0);
    let succ_k_for_ty = d.succ(k);
    let bound_rat_for_ty = div_succ_expr(d, p, succ_k_for_ty, zero_idx);
    let big_b_for_ty = d.const_app(p.of_rat, &[bound_rat_for_ty]);
    let hbound_ty = within_real(d, p, c, big_b_for_ty);
    let hbound_fv = d.fresh_fvar();
    let hbound = d.kernel().fvar(hbound_fv);

    let fsmul = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let cfr = cmul(d, p, c, fr);
        d.lam_fv(r_fv, carrier, cfr)
    };
    let fsmul_p = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let cfpx = cmul(d, p, c, fpx);
        d.lam_fv(x_fv, carrier, cfpx)
    };

    let mf = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);
    // `modulus_smul e := mF ((k+1)*e + k)`.
    let modulus_smul = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let succ_k = d.succ(k);
        let mul_ke = d.mul(succ_k, e);
        let e_prime = d.add(mul_ke, k);
        let mf_e_prime = d.apply(mf, &[e_prime]);
        d.lam_fv(e_fv, nat, mf_e_prime)
    };

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
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

        let diff_yx = cdiff(d, p, y, x);
        let abs_diff = cabs(d, p, diff_yx);

        let succ_k = d.succ(k);
        let mul_ke = d.mul(succ_k, e);
        let e_prime = d.add(mul_ke, k);

        let mod_e = d.apply(modulus_smul, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);
        let h = d.kernel().fvar(h_fv);

        // --- F's own error term and bound, at the rescaled accuracy `e'` ----
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let deriv_term_f = cmul(d, p, fpx, diff_yx);
        let fy_fx_f = cdiff(d, p, fy, fx);
        let error_f = cdiff(d, p, fy_fx_f, deriv_term_f);

        let error_f_bound = d.lemma(
            p.hd_spec,
            &[f, fp, a, b, hf, e_prime, x, y, hax, hxb, hay, hyb, h],
        ); // le (abs error_f) (mul (ofRat (natDivSucc 1 e')) abs_diff)

        let r_prime = div_succ(d, p, 1, e_prime); // natDivSucc 1 e'
        let ofr_e_prime = d.const_app(p.of_rat, &[r_prime]);
        let q_bound = cmul(d, p, ofr_e_prime, abs_diff);

        // --- the scalar bound on `c` --------------------------------------
        let zero_idx = d.num(0);
        let bound_rat = div_succ_expr(d, p, succ_k, zero_idx); // natDivSucc (succ k) 0
        let big_b_expr = d.const_app(p.of_rat, &[bound_rat]);

        // le (abs (mul c error_f)) (mul big_b_expr q_bound)
        let upper = d.lemma(
            p.abs_mul_le_of_bounds,
            &[c, error_f, big_b_expr, q_bound, hbound, error_f_bound],
        );

        // --- fold `(k+1) * natDivSucc 1 e'` down to `natDivSucc 1 e` --------
        let one_nat = d.num(1);
        let mul_succk_1 = d.mul(succ_k, one_nat);
        let succ_k_e_prime = div_succ_expr(d, p, succ_k, e_prime); // natDivSucc (succ k) e'
        let out_bound_rat = div_succ(d, p, 1, e); // natDivSucc 1 e

        let eq_mul = d.lemma(p.rat.nat_div_succ_mul, &[succ_k, one_nat, e_prime]);
        // Eq Rat (Rat.mul bound_rat r_prime) (natDivSucc mul_succk_1 e')
        let mul_one_eq = d.lemma(p.rat.int.nat.mul_one, &[succ_k]);
        // Eq Nat (Nat.mul succ_k 1) succ_k
        let eq_fold = nat_eq_to_rat(d, mul_succk_1, succ_k, mul_one_eq, &|d, x| {
            div_succ_expr(d, p, x, e_prime)
        });
        // Eq Rat (natDivSucc mul_succk_1 e') (natDivSucc succ_k e')
        let eq_scale = d.lemma(p.rat.nat_div_succ_scale, &[k, e]);
        // Eq Rat (natDivSucc succ_k e') (natDivSucc 1 e)

        let of_rat_mul_proof = d.lemma(p.of_rat_mul, &[bound_rat, r_prime]);
        // Equiv (mul big_b_expr ofr_e_prime) (ofRat (Rat.mul bound_rat r_prime))
        let mul_bb_ofre = cmul(d, p, big_b_expr, ofr_e_prime);
        let rat_prod = {
            let f_ap = d.int().rat_mul;
            d.const_app(f_ap, &[bound_rat, r_prime])
        };
        let mul_succk1_e_prime = div_succ_expr(d, p, mul_succk_1, e_prime);

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
        // step_c : Equiv mul_bb_ofre ofr_out
        let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);

        // --- regroup `mul big_b_expr q_bound` to `mul mul_bb_ofre abs_diff` -
        let assoc_eq = d.lemma(p.mul_assoc, &[big_b_expr, ofr_e_prime, abs_diff]);
        // Equiv (mul (mul big_b_expr ofr_e_prime) abs_diff) (mul big_b_expr q_bound)
        let mul_bigb_qbound = cmul(d, p, big_b_expr, q_bound);
        let mul_bbofre_absdiff = cmul(d, p, mul_bb_ofre, abs_diff);
        let assoc_symm = esymm(d, p, mul_bbofre_absdiff, mul_bigb_qbound, assoc_eq);
        // Equiv mul_bigb_qbound mul_bbofre_absdiff

        let out_bound = cmul(d, p, ofr_out, abs_diff);
        let refl_abs_diff = erefl(d, p, abs_diff);
        let mul_congr_eq = d.lemma(
            p.mul_congr,
            &[
                mul_bb_ofre,
                ofr_out,
                abs_diff,
                abs_diff,
                step_c,
                refl_abs_diff,
            ],
        );
        // Equiv mul_bbofre_absdiff out_bound

        let bound_equiv = echain(
            d,
            p,
            mul_bigb_qbound,
            &[(mul_bbofre_absdiff, assoc_symm), (out_bound, mul_congr_eq)],
        ); // Equiv mul_bigb_qbound out_bound

        let mul_c_error_f = cmul(d, p, c, error_f);
        let abs_mul_c_error_f = cabs(d, p, mul_c_error_f);
        let refl_abs_mul = erefl(d, p, abs_mul_c_error_f);
        let final_bound = d.lemma(
            p.le_congr,
            &[
                abs_mul_c_error_f,
                abs_mul_c_error_f,
                mul_bigb_qbound,
                out_bound,
                refl_abs_mul,
                bound_equiv,
                upper,
            ],
        ); // le (abs (mul c error_f)) out_bound

        // --- the actual smul error term IS `c * error_f`, exactly ----------
        let fsmul_y = d.apply(fsmul, &[y]);
        let fsmul_x = d.apply(fsmul, &[x]);
        let fsmul_p_x = d.apply(fsmul_p, &[x]);
        let deriv_term_smul = cmul(d, p, fsmul_p_x, diff_yx);
        let fy_fx_smul = cdiff(d, p, fsmul_y, fsmul_x);
        let error_smul = cdiff(d, p, fy_fx_smul, deriv_term_smul);

        // Step 1: `mul c error_f ~ add (mul c fy_fx_f) (neg (mul c deriv_term_f))`.
        let neg_deriv_term_f = cneg(d, p, deriv_term_f);
        let ld1 = d.lemma(p.left_distrib, &[c, fy_fx_f, neg_deriv_term_f]);
        // Equiv (mul c error_f) (add (mul c fy_fx_f) (mul c neg_deriv_term_f))
        let mul_c_fyfxf = cmul(d, p, c, fy_fx_f);
        let mul_c_negderivf = cmul(d, p, c, neg_deriv_term_f);
        let mne1 = mul_neg_equiv(d, p, c, deriv_term_f);
        // Equiv (mul c neg_deriv_term_f) (neg (mul c deriv_term_f))
        let mul_c_derivf = cmul(d, p, c, deriv_term_f);
        let neg_mul_c_derivf = cneg(d, p, mul_c_derivf);
        let refl_mulc_fyfxf = erefl(d, p, mul_c_fyfxf);
        let step1_congr = d.lemma(
            p.add_congr,
            &[
                mul_c_fyfxf,
                mul_c_fyfxf,
                mul_c_negderivf,
                neg_mul_c_derivf,
                refl_mulc_fyfxf,
                mne1,
            ],
        );
        let target1 = cadd(d, p, mul_c_fyfxf, neg_mul_c_derivf);
        let mul_c_fyfxf_plus_negderivf = cadd(d, p, mul_c_fyfxf, mul_c_negderivf);
        let step1 = echain(
            d,
            p,
            mul_c_error_f,
            &[(mul_c_fyfxf_plus_negderivf, ld1), (target1, step1_congr)],
        ); // Equiv mul_c_error_f target1

        // Step 2: `mul c fy_fx_f ~ add (mul c fy) (neg (mul c fx))` (== fsmul's own diff).
        let neg_fx = cneg(d, p, fx);
        let ld2 = d.lemma(p.left_distrib, &[c, fy, neg_fx]);
        // Equiv (mul c fy_fx_f) (add (mul c fy) (mul c neg_fx))
        let mul_c_fy = cmul(d, p, c, fy);
        let mul_c_negfx = cmul(d, p, c, neg_fx);
        let mne2 = mul_neg_equiv(d, p, c, fx);
        // Equiv (mul c neg_fx) (neg (mul c fx))
        let mul_c_fx = cmul(d, p, c, fx);
        let neg_mul_c_fx = cneg(d, p, mul_c_fx);
        let refl_mulc_fy = erefl(d, p, mul_c_fy);
        let step2_congr = d.lemma(
            p.add_congr,
            &[
                mul_c_fy,
                mul_c_fy,
                mul_c_negfx,
                neg_mul_c_fx,
                refl_mulc_fy,
                mne2,
            ],
        );
        let mul_c_fy_plus_negfx = cadd(d, p, mul_c_fy, mul_c_negfx);
        let step2 = echain(
            d,
            p,
            mul_c_fyfxf,
            &[(mul_c_fy_plus_negfx, ld2), (fy_fx_smul, step2_congr)],
        ); // Equiv mul_c_fyfxf fy_fx_smul  (fy_fx_smul == add (mul c fy) (neg (mul c fx)) == add fsmul_y (neg fsmul_x))

        // Step 3: `mul c deriv_term_f ~ deriv_term_smul` via `mul_assoc`.
        let assoc_d = d.lemma(p.mul_assoc, &[c, fpx, diff_yx]);
        // Equiv (mul (mul c fpx) diff_yx) (mul c (mul fpx diff_yx)) = Equiv deriv_term_smul mul_c_derivf
        let step3 = esymm(d, p, deriv_term_smul, mul_c_derivf, assoc_d);
        // Equiv mul_c_derivf deriv_term_smul
        let step3_neg = d.lemma(p.neg_congr, &[mul_c_derivf, deriv_term_smul, step3]);
        // Equiv neg_mul_c_derivf (neg deriv_term_smul)
        let neg_deriv_term_smul = cneg(d, p, deriv_term_smul);

        // Combine: target1 = add mul_c_fyfxf neg_mul_c_derivf
        //          ~ add fy_fx_smul neg_deriv_term_smul = error_smul.
        let step4 = d.lemma(
            p.add_congr,
            &[
                mul_c_fyfxf,
                fy_fx_smul,
                neg_mul_c_derivf,
                neg_deriv_term_smul,
                step2,
                step3_neg,
            ],
        ); // Equiv target1 error_smul

        let ring_chain = echain(
            d,
            p,
            mul_c_error_f,
            &[(target1, step1), (error_smul, step4)],
        );
        // Equiv mul_c_error_f error_smul
        let ring_chain_symm = esymm(d, p, mul_c_error_f, error_smul, ring_chain);
        // Equiv error_smul mul_c_error_f

        let conclusion = abs_le_of_equiv(
            d,
            p,
            error_smul,
            mul_c_error_f,
            out_bound,
            ring_chain_symm,
            final_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[fsmul, fsmul_p, a, b, modulus_smul, spec]);
    let value = {
        let with_hbound = d.lam_fv(hbound_fv, hbound_ty, mk_applied);
        let with_k = d.lam_fv(k_fv, nat, with_hbound);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_k);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        let with_f = d.lam_fv(f_fv, func_ty, with_fp);
        d.lam_fv(c_fv, carrier, with_f)
    };
    let ty = {
        let applied = hd_ty(d, p, fsmul, fsmul_p, a, b);
        let with_hbound = d.arrow(hbound_ty, applied);
        let with_k = d.pi_fv(k_fv, nat, with_hbound);
        let with_hf = d.arrow(hf_ty, with_k);
        let with_b = d.pi_fv(b_fv, carrier, with_hf);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        let with_f = d.pi_fv(f_fv, func_ty, with_fp);
        d.pi_fv(c_fv, carrier, with_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_smul,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `sub` (cheap from `add` + `neg`) --------------------------------

/// `CReal.hasDerivative_sub : ∀ F F' G G' a b, HasDerivativeOn F F' a b →
/// HasDerivativeOn G G' a b → HasDerivativeOn (fun r => add (F r) (neg (G
/// r))) (fun x => add (F' x) (neg (G' x))) a b`. No new ring algebra: this is
/// exactly `hasDerivative_add F (fun r => neg (G r)) hf (hasDerivative_neg G
/// hg)`.
fn declare_has_derivative_sub(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let gp_fv = d.fresh_fvar();
    let gp = d.kernel().fvar(gp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = hd_ty(d, p, g, gp, a, b);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let neg_g = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let gr = d.apply(g, &[r]);
        let ngr = cneg(d, p, gr);
        d.lam_fv(r_fv, carrier, ngr)
    };
    let neg_gp = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let gpx = d.apply(gp, &[x]);
        let ngpx = cneg(d, p, gpx);
        d.lam_fv(x_fv, carrier, ngpx)
    };

    // hgneg : HasDerivativeOn neg_g neg_gp a b
    let hgneg = d.const_app(p.has_derivative_neg, &[g, gp, a, b, hg]);

    let fsub = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let ngr = cneg(d, p, gr);
        let diff = cadd(d, p, fr, ngr);
        d.lam_fv(r_fv, carrier, diff)
    };
    let fsub_p = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let gpx = d.apply(gp, &[x]);
        let ngpx = cneg(d, p, gpx);
        let diff = cadd(d, p, fpx, ngpx);
        d.lam_fv(x_fv, carrier, diff)
    };

    // hasDerivative_add F neg_g F' neg_gp a b hf hgneg : HasDerivativeOn fsub fsub_p a b
    let mk_applied = d.const_app(
        p.has_derivative_add,
        &[f, fp, neg_g, neg_gp, a, b, hf, hgneg],
    );

    let value = {
        let with_hg = d.lam_fv(hg_fv, hg_ty, mk_applied);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hg);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_gp = d.lam_fv(gp_fv, func_ty, with_a);
        let with_g = d.lam_fv(g_fv, func_ty, with_gp);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_g);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, fsub, fsub_p, a, b);
        let with_hg = d.arrow(hg_ty, applied);
        let with_hf = d.arrow(hf_ty, with_hg);
        let with_b = d.pi_fv(b_fv, carrier, with_hf);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_gp = d.pi_fv(gp_fv, func_ty, with_a);
        let with_g = d.pi_fv(g_fv, func_ty, with_gp);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_g);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_sub,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `mul` (the product rule) ----------------------------------------
//
// See the module documentation's corrected, numerically re-verified error
// decomposition:
//
//   F(y)G(y) - F(x)G(x) - (F'(x)G(x) + F(x)G'(x))(y-x)
//     = F(y)*[G(y) - G(x) - G'(x)(y-x)]        -- term1
//     + G(x)*[F(y) - F(x) - F'(x)(y-x)]        -- term2
//     + (F(y) - F(x))*G'(x)*(y-x)              -- term3
//
// closed by three EXPLICIT hypotheses (boundedness of F, G, G' on [a,b], each
// as `|h z| <= (k+1)/(0+1)` for a universally quantified `Nat` `k`) plus
// uniform continuity of `F` on `[a,b]` -- none of these are derived, matching
// this slice's brief. The accuracy budget splits the target `1/(e+1)` into
// THREE EQUAL shares `1/(3e+3)` -- `rescale_index` below is
// `Rat.natDivSucc_scale`'s own index shape `(c+1)*m+c`, used BOTH to build
// the equal three-way split itself (`c := 2`, giving `3e+2`) and, once more,
// to rescale each term's OWN accuracy against its own magnitude bound
// (`c := k1/k2/k3`), exactly `hasDerivative_smul`'s single rescale, three
// times over with three independent `Nat` bounds.

/// `(k+1)*m + k` -- the index shape `Rat.natDivSucc_scale` recognises
/// (`hasDerivative_smul`'s own `e' := (k+1)*e + k`, generalised to an
/// arbitrary target `m` rather than always the outer accuracy `e`). Used
/// here twice over: once at `k := 2` to build the equal three-way split
/// `3e+2` from the outer accuracy `e`, and again at `k := k1/k2/k3` to
/// rescale each term's own accuracy against its own magnitude bound, reading
/// that rescaled accuracy back down to `1/(3e+3)` (`nat_div_succ_scale`
/// undoes exactly this shape).
fn rescale_index(d: &mut IntDev<'_>, k: ExprId, m: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let mul_km = d.mul(succ_k, m);
    d.add(mul_km, k)
}

/// `ofRat (natDivSucc (Nat.succ k) 0)` -- the "index 0, numerator `k+1`"
/// magnitude-bound shape `hasDerivative_smul`'s own scalar hypothesis uses,
/// reused here for three separate hypotheses (`F`, `G` and `G'`, each
/// bounded by its own `Nat` on `[a,b]`).
fn mag_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let r = div_succ_expr(d, p, succ_k, zero_idx);
    d.const_app(p.of_rat, &[r])
}

/// `forall z, le a z -> le z b -> le (abs (h z)) (mag_bound k)` -- "`h` is
/// bounded by `k+1` on `[a,b]`", the hypothesis shape shared by the product
/// rule's three magnitude bounds (on `F`, `G` and `G'`).
fn bounded_on_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    h: ExprId,
    a: ExprId,
    b: ExprId,
    k: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let range_az = d.const_app(p.le, &[a, z]);
    let range_zb = d.const_app(p.le, &[z, b]);
    let hz = d.apply(h, &[z]);
    let bound = mag_bound(d, p, k);
    let concl = within_real(d, p, hz, bound);
    let with_zb = d.arrow(range_zb, concl);
    let with_az = d.arrow(range_az, with_zb);
    d.pi_fv(z_fv, carrier, with_az)
}

/// From `mul (ofRat (natDivSucc (succ k) 0)) (ofRat (natDivSucc 1 e_prime))`
/// (the "index-0 magnitude bound comes FIRST" product, `hasDerivative_smul`'s
/// own shape), derive `Equiv` to `ofRat (natDivSucc 1 m)`, where `e_prime`
/// MUST be built as `rescale_index(k, m)` (`Rat.natDivSucc_scale`'s own
/// index) for the final fold to typecheck. Returns `(big_expr, small_expr,
/// ofr_out, proof)`.
fn fold_index0_first(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    m: ExprId,
    e_prime: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let bound_rat = div_succ_expr(d, p, succ_k, zero_idx); // natDivSucc (succ k) 0
    let big_expr = d.const_app(p.of_rat, &[bound_rat]);

    let r_prime = div_succ(d, p, 1, e_prime); // natDivSucc 1 e_prime
    let small_expr = d.const_app(p.of_rat, &[r_prime]);

    let one_nat = d.num(1);
    let mul_succk_1 = d.mul(succ_k, one_nat);
    let succ_k_e_prime = div_succ_expr(d, p, succ_k, e_prime);
    let out_bound_rat = div_succ(d, p, 1, m);

    let eq_mul = d.lemma(p.rat.nat_div_succ_mul, &[succ_k, one_nat, e_prime]);
    let mul_one_eq = d.lemma(p.rat.int.nat.mul_one, &[succ_k]);
    let eq_fold = nat_eq_to_rat(d, mul_succk_1, succ_k, mul_one_eq, &|d, x| {
        div_succ_expr(d, p, x, e_prime)
    });
    let eq_scale = d.lemma(p.rat.nat_div_succ_scale, &[k, m]);

    let of_rat_mul_proof = d.lemma(p.of_rat_mul, &[bound_rat, r_prime]);
    let mul_bb_ofre = cmul(d, p, big_expr, small_expr);
    let rat_prod = {
        let f_ap = d.int().rat_mul;
        d.const_app(f_ap, &[bound_rat, r_prime])
    };
    let mul_succk1_e_prime = div_succ_expr(d, p, mul_succk_1, e_prime);

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

/// The mirror of [`fold_index0_first`] with the two factors SWAPPED: from
/// `mul (ofRat (natDivSucc 1 e_prime)) (ofRat (natDivSucc (succ k) 0))`
/// (index-0 magnitude bound comes SECOND, term3's own shape -- continuity's
/// bound on `|F(y)-F(x)|` has no natural "index 0" companion to put first),
/// derive `Equiv` to `ofRat (natDivSucc 1 m)` via one extra `Rat.mul_comm`
/// step ahead of [`fold_index0_first`]'s own fold. Returns `(small_expr,
/// big_expr, ofr_out, proof)`.
fn fold_index0_second(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    m: ExprId,
    e_prime: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let r_prime = div_succ(d, p, 1, e_prime);
    let small_expr = d.const_app(p.of_rat, &[r_prime]);
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let bound_rat = div_succ_expr(d, p, succ_k, zero_idx);
    let big_expr = d.const_app(p.of_rat, &[bound_rat]);

    let mul_small_big = cmul(d, p, small_expr, big_expr);

    let of_rat_mul_proof = d.lemma(p.of_rat_mul, &[r_prime, bound_rat]);
    // Equiv (mul small_expr big_expr) (ofRat (Rat.mul r_prime bound_rat))
    let rat_mul_int = d.int().rat_mul;
    let rat_prod_rb = d.const_app(rat_mul_int, &[r_prime, bound_rat]);
    let rat_prod_br = d.const_app(rat_mul_int, &[bound_rat, r_prime]);
    let comm_eq = d.lemma(p.rat.mul_comm, &[r_prime, bound_rat]);
    // Eq (Rat.mul r_prime bound_rat) (Rat.mul bound_rat r_prime)

    let motive = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[mul_small_big, oft])
    };
    let step_a = rat_eq_rewrite(
        d,
        rat_prod_rb,
        rat_prod_br,
        comm_eq,
        of_rat_mul_proof,
        &motive,
    );
    // Equiv mul_small_big (ofRat rat_prod_br)

    let one_nat = d.num(1);
    let mul_succk_1 = d.mul(succ_k, one_nat);
    let succ_k_e_prime = div_succ_expr(d, p, succ_k, e_prime);
    let out_bound_rat = div_succ(d, p, 1, m);

    let eq_mul = d.lemma(p.rat.nat_div_succ_mul, &[succ_k, one_nat, e_prime]);
    let mul_one_eq = d.lemma(p.rat.int.nat.mul_one, &[succ_k]);
    let eq_fold = nat_eq_to_rat(d, mul_succk_1, succ_k, mul_one_eq, &|d, x| {
        div_succ_expr(d, p, x, e_prime)
    });
    let eq_scale = d.lemma(p.rat.nat_div_succ_scale, &[k, m]);

    let mul_succk1_e_prime = div_succ_expr(d, p, mul_succk_1, e_prime);

    let step_b = rat_eq_rewrite(d, rat_prod_br, mul_succk1_e_prime, eq_mul, step_a, &motive);
    let step_c = rat_eq_rewrite(
        d,
        mul_succk1_e_prime,
        succ_k_e_prime,
        eq_fold,
        step_b,
        &motive,
    );
    let step_d = rat_eq_rewrite(d, succ_k_e_prime, out_bound_rat, eq_scale, step_c, &motive);
    let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);

    (small_expr, big_expr, ofr_out, step_d)
}

/// The product rule's three-source combined modulus at a given accuracy
/// `e`: `mG (e1') + mF (e2') + muc (e3)`, where `e1'/e2'/e3 :=
/// rescale_index(k1/k2/k3, three_e)` and `three_e := rescale_index(2, e)`
/// (the equal three-way split). Returns `(three_e, e1p, e2p, e3, mg_val,
/// mf_val, mu_val, mgf, combined)`. Called identically to build the
/// `modulus_mul` lambda's own body and, separately, to recompute the same
/// quantities inside `spec` at a fixed `e` -- the two calls must produce
/// SYNTACTICALLY identical terms (guaranteed by calling this one function
/// both times) for `Kernel::add_declaration` to accept `spec`'s type against
/// `hd_mk`'s expected `deriv_spec_body ... modulus_mul`.
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn mul_modulus_components(
    d: &mut IntDev<'_>,
    mg: ExprId,
    mf: ExprId,
    mu: ExprId,
    k1: ExprId,
    k2: ExprId,
    k3: ExprId,
    e: ExprId,
) -> (
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
    ExprId,
) {
    let two = d.num(2);
    let three_e = rescale_index(d, two, e);
    let e1p = rescale_index(d, k1, three_e);
    let e2p = rescale_index(d, k2, three_e);
    let e3 = rescale_index(d, k3, three_e);
    let mg_val = d.apply(mg, &[e1p]);
    let mf_val = d.apply(mf, &[e2p]);
    let mu_val = d.apply(mu, &[e3]);
    let mgf = d.add(mg_val, mf_val);
    let combined = d.add(mgf, mu_val);
    (three_e, e1p, e2p, e3, mg_val, mf_val, mu_val, mgf, combined)
}

/// From `h : le abs_diff (ofRat (natDivSucc 1 combined))` where `combined =
/// add (add mg_val mf_val) mu_val`, derive the three weakened hypotheses at
/// each individual addend (`le abs_diff (ofRat (natDivSucc 1 mg_val))`,
/// etc.) via `Nat.le_add_right`/`Nat.add_comm` (placing each addend first)
/// and `Rat.natDivSucc_antitone` -- the three-source generalisation of
/// `hasDerivative_add`'s own two-source combination.
#[allow(clippy::too_many_arguments)]
fn weaken_to_addend(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    abs_diff: ExprId,
    combined: ExprId,
    mgf: ExprId,
    mg_val: ExprId,
    mf_val: ExprId,
    mu_val: ExprId,
    h: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let nat_p = p.rat.int.nat;

    // mg_val <= combined
    let s1 = d.lemma(nat_p.le_add_right, &[mg_val, mf_val]); // mg_val <= mgf
    let s2 = d.lemma(nat_p.le_add_right, &[mgf, mu_val]); // mgf <= combined
    let mg_le_combined = d.lemma(nat_p.le_trans, &[mg_val, mgf, combined, s1, s2]);

    // mf_val <= combined
    let s3 = d.lemma(nat_p.le_add_right, &[mf_val, mg_val]); // mf_val <= mf_val+mg_val
    let comm1 = d.lemma(nat_p.add_comm, &[mf_val, mg_val]); // Eq (mf_val+mg_val) mgf
    let mf_plus_mg = d.add(mf_val, mg_val);
    let s3p = nat_rewrite_prop(d, mf_plus_mg, mgf, comm1, s3, &|d, t| d.le(mf_val, t));
    let mf_le_combined = d.lemma(nat_p.le_trans, &[mf_val, mgf, combined, s3p, s2]);

    // mu_val <= combined
    let s4 = d.lemma(nat_p.le_add_right, &[mu_val, mgf]); // mu_val <= mu_val+mgf
    let comm2 = d.lemma(nat_p.add_comm, &[mu_val, mgf]); // Eq (mu_val+mgf) combined
    let mu_plus_mgf = d.add(mu_val, mgf);
    let mu_le_combined =
        nat_rewrite_prop(d, mu_plus_mgf, combined, comm2, s4, &|d, t| d.le(mu_val, t));

    let weaken = |d: &mut IntDev<'_>, val: ExprId, le_val_combined: ExprId| -> ExprId {
        let rat_le = d.lemma(
            p.rat.nat_div_succ_antitone,
            &[val, combined, le_val_combined],
        );
        let r_combined = div_succ(d, p, 1, combined);
        let r_val = div_succ(d, p, 1, val);
        let creal_le = d.lemma(p.of_rat_le, &[r_combined, r_val, rat_le]);
        let ofr_combined = d.const_app(p.of_rat, &[r_combined]);
        let ofr_val = d.const_app(p.of_rat, &[r_val]);
        d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_val, h, creal_le])
    };

    let h_g = weaken(d, mg_val, mg_le_combined);
    let h_f = weaken(d, mf_val, mf_le_combined);
    let h_c = weaken(d, mu_val, mu_le_combined);
    (h_g, h_f, h_c)
}

/// From `big = mul p_val (cdiff (cdiff q_hi q_lo) (cmul q_deriv diff))` (the
/// shape `p_val * [error term of q]`, shared by the product rule's term1
/// -- `p_val := F y`, `q_hi/q_lo/q_deriv := G y/G x/G' x` -- and term2 with
/// `F`/`G` swapped), derive `Equiv big target` where `target = add (add
/// (mul p_val q_hi) (neg (mul p_val q_lo))) (neg f_term)` and `f_term = mul
/// (mul p_val q_deriv) diff`. Returns `(big, target, f_term, proof)` -- `big`
/// is returned so the CALLER can use this exact term (rather than a
/// separately-reconstructed copy) as e.g. term1/term2 in the surrounding
/// bound derivation, and `f_term` is returned separately because term1's own
/// `f_term` (`p_val := F y`, `q_deriv := G' x`) is the EXACT SAME term
/// `expand_term3`'s `hi_term` produces, needed so the two cancel with no
/// extra congruence step.
fn expand_bound_term(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    p_val: ExprId,
    q_hi: ExprId,
    q_lo: ExprId,
    q_deriv: ExprId,
    diff: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let q_lo_neg = cneg(d, p, q_lo);
    let hi_lo = cadd(d, p, q_hi, q_lo_neg); // q_hi - q_lo
    let deriv_term = cmul(d, p, q_deriv, diff);
    let deriv_term_neg = cneg(d, p, deriv_term);
    let inner = cadd(d, p, hi_lo, deriv_term_neg);
    let big = cmul(d, p, p_val, inner);

    // top split: p_val * (hi_lo + (-deriv_term)) ~ p_val*hi_lo + p_val*(-deriv_term)
    let ld_top = d.lemma(p.left_distrib, &[p_val, hi_lo, deriv_term_neg]);
    let mul_p_hilo = cmul(d, p, p_val, hi_lo);
    let mul_p_negderiv = cmul(d, p, p_val, deriv_term_neg);

    // p_val*(-deriv_term) ~ -(p_val*deriv_term)
    let mne_deriv = mul_neg_equiv(d, p, p_val, deriv_term);
    let mul_p_deriv = cmul(d, p, p_val, deriv_term);
    let neg_mul_p_deriv = cneg(d, p, mul_p_deriv);

    // p_val*hi_lo ~ p_val*q_hi + p_val*(-q_lo)
    let ld_bottom = d.lemma(p.left_distrib, &[p_val, q_hi, q_lo_neg]);
    let mul_p_qhi = cmul(d, p, p_val, q_hi);
    let mul_p_neg_qlo = cmul(d, p, p_val, q_lo_neg);

    // p_val*(-q_lo) ~ -(p_val*q_lo)
    let mne_lo = mul_neg_equiv(d, p, p_val, q_lo);
    let mul_p_qlo = cmul(d, p, p_val, q_lo);
    let neg_mul_p_qlo = cneg(d, p, mul_p_qlo);

    let refl_mul_p_qhi = erefl(d, p, mul_p_qhi);
    let hi_lo_congr = d.lemma(
        p.add_congr,
        &[
            mul_p_qhi,
            mul_p_qhi,
            mul_p_neg_qlo,
            neg_mul_p_qlo,
            refl_mul_p_qhi,
            mne_lo,
        ],
    );
    let target_hilo = cadd(d, p, mul_p_qhi, neg_mul_p_qlo);
    let mul_p_qhi_plus_mul_p_neg_qlo = cadd(d, p, mul_p_qhi, mul_p_neg_qlo);
    let hilo_chain = echain(
        d,
        p,
        mul_p_hilo,
        &[
            (mul_p_qhi_plus_mul_p_neg_qlo, ld_bottom),
            (target_hilo, hi_lo_congr),
        ],
    );

    // p_val * deriv_term ~ (p_val*q_deriv)*diff, via mul_assoc reversed
    let mul_p_qderiv = cmul(d, p, p_val, q_deriv);
    let f_term = cmul(d, p, mul_p_qderiv, diff);
    let assoc_d = d.lemma(p.mul_assoc, &[p_val, q_deriv, diff]);
    // Equiv f_term mul_p_deriv
    let deriv_symm = esymm(d, p, f_term, mul_p_deriv, assoc_d); // Equiv mul_p_deriv f_term
    let neg_deriv_congr = d.lemma(p.neg_congr, &[mul_p_deriv, f_term, deriv_symm]);
    let neg_f_term = cneg(d, p, f_term);

    let mne_deriv_to_negfterm = echain(
        d,
        p,
        mul_p_negderiv,
        &[(neg_mul_p_deriv, mne_deriv), (neg_f_term, neg_deriv_congr)],
    );

    let top_congr = d.lemma(
        p.add_congr,
        &[
            mul_p_hilo,
            target_hilo,
            mul_p_negderiv,
            neg_f_term,
            hilo_chain,
            mne_deriv_to_negfterm,
        ],
    );
    let target = cadd(d, p, target_hilo, neg_f_term);
    let mul_p_hilo_plus_mul_p_negderiv = cadd(d, p, mul_p_hilo, mul_p_negderiv);
    let final_chain = echain(
        d,
        p,
        big,
        &[
            (mul_p_hilo_plus_mul_p_negderiv, ld_top),
            (target, top_congr),
        ],
    );
    (big, target, f_term, final_chain)
}

/// Term3's own expansion: `Equiv (mul (mul (cdiff hi lo) deriv) diff) (add
/// hi_term (neg lo_term))`, where `hi_term = mul (mul hi deriv) diff` and
/// `lo_term = mul (mul lo deriv) diff` -- `(F(y)-F(x))*G'(x)*(y-x) ~
/// F(y)*G'(x)*(y-x) - F(x)*G'(x)*(y-x)`. With `hi := F y`, `deriv := G' x`,
/// `hi_term` is syntactically the exact `f_term` [`expand_bound_term`]
/// returns for term1 (`p_val := F y`, `q_deriv := G' x`) -- no extra
/// congruence is needed to cancel them. Returns `(big, hi_term, lo_term,
/// proof)`.
fn expand_term3(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    hi: ExprId,
    lo: ExprId,
    deriv: ExprId,
    diff: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let lo_neg = cneg(d, p, lo);
    let hilo = cadd(d, p, hi, lo_neg); // hi - lo
    let mul_hilo_deriv = cmul(d, p, hilo, deriv);
    let big = cmul(d, p, mul_hilo_deriv, diff);

    // (hi-lo)*deriv ~ hi*deriv + (-lo)*deriv
    let rd1 = right_distrib(d, p, hi, lo_neg, deriv);
    let mul_hi_deriv = cmul(d, p, hi, deriv);
    let mul_neglo_deriv = cmul(d, p, lo_neg, deriv);

    // (-lo)*deriv ~ -(lo*deriv)
    let nme1 = neg_mul_equiv_left(d, p, lo, deriv);
    let mul_lo_deriv = cmul(d, p, lo, deriv);
    let neg_mul_lo_deriv = cneg(d, p, mul_lo_deriv);

    let refl_mhd = erefl(d, p, mul_hi_deriv);
    let step1_congr = d.lemma(
        p.add_congr,
        &[
            mul_hi_deriv,
            mul_hi_deriv,
            mul_neglo_deriv,
            neg_mul_lo_deriv,
            refl_mhd,
            nme1,
        ],
    );
    let target1 = cadd(d, p, mul_hi_deriv, neg_mul_lo_deriv);
    let mul_hi_deriv_plus_mul_neglo_deriv = cadd(d, p, mul_hi_deriv, mul_neglo_deriv);
    let step1 = echain(
        d,
        p,
        mul_hilo_deriv,
        &[
            (mul_hi_deriv_plus_mul_neglo_deriv, rd1),
            (target1, step1_congr),
        ],
    );

    let refl_diff = erefl(d, p, diff);
    let big_congr = d.lemma(
        p.mul_congr,
        &[mul_hilo_deriv, target1, diff, diff, step1, refl_diff],
    );
    let mul_target1_diff = cmul(d, p, target1, diff);

    // target1 * diff ~ (mul_hi_deriv*diff) + (neg_mul_lo_deriv*diff)
    let rd2 = right_distrib(d, p, mul_hi_deriv, neg_mul_lo_deriv, diff);
    let hi_term = cmul(d, p, mul_hi_deriv, diff);
    let mul_negmld_diff = cmul(d, p, neg_mul_lo_deriv, diff);

    // neg_mul_lo_deriv*diff ~ -(mul_lo_deriv*diff)
    let nme2 = neg_mul_equiv_left(d, p, mul_lo_deriv, diff);
    let lo_term = cmul(d, p, mul_lo_deriv, diff);
    let neg_lo_term = cneg(d, p, lo_term);

    let refl_hiterm = erefl(d, p, hi_term);
    let final_congr = d.lemma(
        p.add_congr,
        &[
            hi_term,
            hi_term,
            mul_negmld_diff,
            neg_lo_term,
            refl_hiterm,
            nme2,
        ],
    );
    let target = cadd(d, p, hi_term, neg_lo_term);
    let hi_term_plus_mul_negmld_diff = cadd(d, p, hi_term, mul_negmld_diff);

    let final_chain = echain(
        d,
        p,
        big,
        &[
            (mul_target1_diff, big_congr),
            (hi_term_plus_mul_negmld_diff, rd2),
            (target, final_congr),
        ],
    );

    (big, hi_term, lo_term, final_chain)
}

/// From three INDEPENDENTLY-BUILT copies `q1, q2, q3` of `ofRat (natDivSucc
/// 1 three_e)` (with `r1, r2, r3` their underlying `Rat` cores, `three_e :=
/// rescale_index(2, e)`), derive `Equiv (add (add (mul q1 abs_diff) (mul q2
/// abs_diff)) (mul q3 abs_diff)) (mul (ofRat (natDivSucc 1 e)) abs_diff)` --
/// the "three EQUAL shares of `1/(e+1)` sum back to the target" arithmetic
/// (`Rat.natDivSucc_add` applied twice, `Rat.natDivSucc_scale` at `c := 2`),
/// the three-way generalisation of `hasDerivative_add`'s own two-way
/// `natDivSucc_add`+`natDivSucc_halve` fuse (`natDivSucc_halve` IS
/// `natDivSucc_scale` at `c := 1`; this is the SAME identity one step
/// deeper, `c := 2`). Returns `(out_bound, proof)`.
#[allow(clippy::too_many_arguments)]
fn fuse_three_equal_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e: ExprId,
    three_e: ExprId,
    q1: ExprId,
    q2: ExprId,
    q3: ExprId,
    r1: ExprId,
    r2: ExprId,
    r3: ExprId,
    abs_diff: ExprId,
) -> (ExprId, ExprId) {
    let c1 = cmul(d, p, q1, abs_diff);
    let c2 = cmul(d, p, q2, abs_diff);
    let c3 = cmul(d, p, q3, abs_diff);
    let sum_c1_c2 = cadd(d, p, c1, c2);
    let sum123 = cadd(d, p, sum_c1_c2, c3);

    let q12 = cadd(d, p, q1, q2);
    let mul_q12_ad = cmul(d, p, q12, abs_diff);

    // (c1+c2) ~ mul_q12_ad, and (mul_q12_ad + c3) ~ mul (add q12 q3) abs_diff.
    let rd_12 = right_distrib(d, p, q1, q2, abs_diff); // Equiv mul_q12_ad (add c1 c2)
    let rd_12_symm = esymm(d, p, mul_q12_ad, sum_c1_c2, rd_12); // Equiv (add c1 c2) mul_q12_ad

    let q_triple = cadd(d, p, q12, q3);
    let mul_qtriple_ad = cmul(d, p, q_triple, abs_diff);
    let rd_full = right_distrib(d, p, q12, q3, abs_diff);
    // Equiv mul_qtriple_ad (add mul_q12_ad c3)
    let mul_q12ad_c3 = cadd(d, p, mul_q12_ad, c3);
    let rd_full_symm = esymm(d, p, mul_qtriple_ad, mul_q12ad_c3, rd_full);
    // Equiv (add mul_q12_ad c3) mul_qtriple_ad

    let refl_c3 = erefl(d, p, c3);
    let congr_step = d.lemma(
        p.add_congr,
        &[sum_c1_c2, mul_q12_ad, c3, c3, rd_12_symm, refl_c3],
    ); // Equiv sum123 mul_q12ad_c3
    let chain1 = echain(
        d,
        p,
        sum123,
        &[(mul_q12ad_c3, congr_step), (mul_qtriple_ad, rd_full_symm)],
    ); // Equiv sum123 mul_qtriple_ad

    // --- the pure rational-level fuse: q_triple ~ ofRat (natDivSucc 1 e) ---
    let one_nat = d.num(1);
    let two = d.num(2);

    let of_rat_add_proof1 = d.lemma(p.of_rat_add, &[r1, r2]);
    // Equiv (add q1 q2) (ofRat (Rat.add r1 r2))
    let eq1 = d.lemma(p.rat.nat_div_succ_add, &[one_nat, one_nat, three_e]);
    let two_three_e = div_succ(d, p, 2, three_e);
    let radd_r1_r2 = radd(d, r1, r2);
    let motive_a = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[q12, oft])
    };
    let step_a = rat_eq_rewrite(
        d,
        radd_r1_r2,
        two_three_e,
        eq1,
        of_rat_add_proof1,
        &motive_a,
    );
    // Equiv q12 (ofRat two_three_e)

    let ofr2 = d.const_app(p.of_rat, &[two_three_e]);
    let refl_q3 = erefl(d, p, q3);
    let congr_b = d.lemma(p.add_congr, &[q12, ofr2, q3, q3, step_a, refl_q3]);
    // Equiv q_triple (add ofr2 q3)
    let add_ofr2_q3 = cadd(d, p, ofr2, q3);

    let of_rat_add_proof2 = d.lemma(p.of_rat_add, &[two_three_e, r3]);
    // Equiv (add ofr2 q3) (ofRat (Rat.add two_three_e r3))
    let succ_two = d.succ(two);
    let eq2 = d.lemma(p.rat.nat_div_succ_add, &[two, one_nat, three_e]);
    let radd_two3e_r3 = radd(d, two_three_e, r3);
    let three_three_e = div_succ_expr(d, p, succ_two, three_e);

    let motive_c = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[q_triple, oft])
    };
    let ofr_radd_two3e_r3 = d.const_app(p.of_rat, &[radd_two3e_r3]);
    let chain_qtriple = echain(
        d,
        p,
        q_triple,
        &[
            (add_ofr2_q3, congr_b),
            (ofr_radd_two3e_r3, of_rat_add_proof2),
        ],
    ); // Equiv q_triple (ofRat (Rat.add two_three_e r3))
    let step_c = rat_eq_rewrite(
        d,
        radd_two3e_r3,
        three_three_e,
        eq2,
        chain_qtriple,
        &motive_c,
    );
    // Equiv q_triple (ofRat three_three_e)

    let eq3 = d.lemma(p.rat.nat_div_succ_scale, &[two, e]);
    let out_bound_rat = div_succ(d, p, 1, e);
    let step_d = rat_eq_rewrite(d, three_three_e, out_bound_rat, eq3, step_c, &motive_c);
    // Equiv q_triple (ofRat out_bound_rat)

    let ofr_target = d.const_app(p.of_rat, &[out_bound_rat]);
    let refl_absdiff = erefl(d, p, abs_diff);
    let mul_lift = d.lemma(
        p.mul_congr,
        &[
            q_triple,
            ofr_target,
            abs_diff,
            abs_diff,
            step_d,
            refl_absdiff,
        ],
    ); // Equiv mul_qtriple_ad (mul ofr_target abs_diff)

    let out_bound = cmul(d, p, ofr_target, abs_diff);
    let final_chain = echain(
        d,
        p,
        sum123,
        &[(mul_qtriple_ad, chain1), (out_bound, mul_lift)],
    );

    (out_bound, final_chain)
}

/// `CReal.hasDerivative_mul : forall F F' G G' a b, HasDerivativeOn F F' a b
/// -> HasDerivativeOn G G' a b -> UniformlyContinuousOn F a b -> forall (k1
/// k2 k3 : Nat), (forall z, le a z -> le z b -> le (abs (F z)) (mag_bound
/// k1)) -> (forall z, le a z -> le z b -> le (abs (G z)) (mag_bound k2)) ->
/// (forall z, le a z -> le z b -> le (abs (G' z)) (mag_bound k3)) ->
/// HasDerivativeOn (fun r => mul (F r) (G r)) (fun x => add (mul (F' x)(G
/// x)) (mul (F x)(G' x))) a b` -- **the product rule**, closed by three
/// EXPLICIT magnitude-bound hypotheses (`F`, `G`, `G'` each `|h z| <= k+1` on
/// `[a,b]`) plus uniform continuity of `F` on `[a,b]`, none of which is
/// derived -- see the module documentation's corrected, numerically
/// re-verified error decomposition, and this file's `rescale_index`/
/// `fold_index0_first`/`fold_index0_second`/`mul_modulus_components`/
/// `weaken_to_addend`/`expand_bound_term`/`expand_term3`/
/// `fuse_three_equal_bounds` helpers, all built for this witness.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_has_derivative_mul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let gp_fv = d.fresh_fvar();
    let gp = d.kernel().fvar(gp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = hd_ty(d, p, g, gp, a, b);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);
    let huc_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);

    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);
    let k3_fv = d.fresh_fvar();
    let k3 = d.kernel().fvar(k3_fv);

    let hbf_ty = bounded_on_ty(d, p, f, a, b, k1);
    let hbf_fv = d.fresh_fvar();
    let hbf = d.kernel().fvar(hbf_fv);
    let hbg_ty = bounded_on_ty(d, p, g, a, b, k2);
    let hbg_fv = d.fresh_fvar();
    let hbg = d.kernel().fvar(hbg_fv);
    let hbgp_ty = bounded_on_ty(d, p, gp, a, b, k3);
    let hbgp_fv = d.fresh_fvar();
    let hbgp = d.kernel().fvar(hbgp_fv);

    let fmul = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let prod = cmul(d, p, fr, gr);
        d.lam_fv(r_fv, carrier, prod)
    };
    let fmul_p = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let gx = d.apply(g, &[x]);
        let fx = d.apply(f, &[x]);
        let gpx = d.apply(gp, &[x]);
        let t1 = cmul(d, p, fpx, gx);
        let t2 = cmul(d, p, fx, gpx);
        let sum = cadd(d, p, t1, t2);
        d.lam_fv(x_fv, carrier, sum)
    };

    let mf = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);
    let mg = d.const_app(p.hd_modulus, &[g, gp, a, b, hg]);
    let mu = d.const_app(p.uc_modulus, &[f, a, b, huc]);

    let modulus_mul = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let (_, _, _, _, _, _, _, _, combined) =
            mul_modulus_components(d, mg, mf, mu, k1, k2, k3, e);
        d.lam_fv(e_fv, nat, combined)
    };

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
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

        let diff_yx = cdiff(d, p, y, x);
        let abs_diff = cabs(d, p, diff_yx);

        let (three_e, e1p, e2p, e3, mg_val, mf_val, mu_val, mgf, combined) =
            mul_modulus_components(d, mg, mf, mu, k1, k2, k3, e);

        let mod_e = d.apply(modulus_mul, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);
        let h = d.kernel().fvar(h_fv);

        let (h_g, h_f, h_c) =
            weaken_to_addend(d, p, abs_diff, combined, mgf, mg_val, mf_val, mu_val, h);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);
        let fpx = d.apply(fp, &[x]);
        let gpx = d.apply(gp, &[x]);

        // --- term1 = F(y) * [G's error at e1p] -------------------------------
        let g_error_bound = d.lemma(
            p.hd_spec,
            &[g, gp, a, b, hg, e1p, x, y, hax, hxb, hay, hyb, h_g],
        );
        // le (abs g_error) (mul (ofRat (natDivSucc 1 e1p)) abs_diff)

        let hbf_y = d.apply(hbf, &[y, hay, hyb]); // le (abs fy) (mag_bound k1)
        let big_b1 = mag_bound(d, p, k1);
        let small1 = {
            let r = div_succ(d, p, 1, e1p);
            d.const_app(p.of_rat, &[r])
        };
        let small1_times_absdiff = cmul(d, p, small1, abs_diff);

        let (term1, target1, f_term1, proof1) = expand_bound_term(d, p, fy, gy, gx, gpx, diff_yx);
        let g_error = {
            let gyx = cdiff(d, p, gy, gx);
            let gderiv = cmul(d, p, gpx, diff_yx);
            cdiff(d, p, gyx, gderiv)
        };

        let term1_upper = d.lemma(
            p.abs_mul_le_of_bounds,
            &[
                fy,
                g_error,
                big_b1,
                small1_times_absdiff,
                hbf_y,
                g_error_bound,
            ],
        );
        // le (abs term1) (mul big_b1 (mul small1 abs_diff))

        let assoc_eq1 = d.lemma(p.mul_assoc, &[big_b1, small1, abs_diff]);
        // Equiv (mul (mul big_b1 small1) abs_diff) (mul big_b1 (mul small1 abs_diff))
        let mul_bigb1_small1 = cmul(d, p, big_b1, small1);
        let regroup1 = cmul(d, p, mul_bigb1_small1, abs_diff);
        let big_b1_small1_ad = cmul(d, p, big_b1, small1_times_absdiff);
        let assoc_symm1 = esymm(d, p, regroup1, big_b1_small1_ad, assoc_eq1);

        let (big_expr1, small_expr1, ofr_out1, fold_proof1) =
            fold_index0_first(d, p, k1, three_e, e1p);
        let refl_absdiff_a = erefl(d, p, abs_diff);
        let mul_bigexpr1_smallexpr1 = cmul(d, p, big_expr1, small_expr1);
        let mul_congr1 = d.lemma(
            p.mul_congr,
            &[
                mul_bigexpr1_smallexpr1,
                ofr_out1,
                abs_diff,
                abs_diff,
                fold_proof1,
                refl_absdiff_a,
            ],
        );
        let out_bound1 = cmul(d, p, ofr_out1, abs_diff);
        let bound_equiv1 = echain(
            d,
            p,
            big_b1_small1_ad,
            &[(regroup1, assoc_symm1), (out_bound1, mul_congr1)],
        );

        let abs_term1 = cabs(d, p, term1);
        let refl_abs_term1 = erefl(d, p, abs_term1);
        let term1_bound = d.lemma(
            p.le_congr,
            &[
                abs_term1,
                abs_term1,
                big_b1_small1_ad,
                out_bound1,
                refl_abs_term1,
                bound_equiv1,
                term1_upper,
            ],
        );
        // le (abs term1) out_bound1

        // --- term2 = G(x) * [F's error at e2p] -------------------------------
        let f_error_bound = d.lemma(
            p.hd_spec,
            &[f, fp, a, b, hf, e2p, x, y, hax, hxb, hay, hyb, h_f],
        );
        // le (abs f_error) (mul (ofRat (natDivSucc 1 e2p)) abs_diff)

        let hbg_x = d.apply(hbg, &[x, hax, hxb]); // le (abs gx) (mag_bound k2)
        let big_b2 = mag_bound(d, p, k2);
        let small2 = {
            let r = div_succ(d, p, 1, e2p);
            d.const_app(p.of_rat, &[r])
        };
        let small2_times_absdiff = cmul(d, p, small2, abs_diff);

        let (term2, target2, g_term2, proof2) = expand_bound_term(d, p, gx, fy, fx, fpx, diff_yx);
        let f_error = {
            let fyx = cdiff(d, p, fy, fx);
            let fderiv = cmul(d, p, fpx, diff_yx);
            cdiff(d, p, fyx, fderiv)
        };

        let term2_upper = d.lemma(
            p.abs_mul_le_of_bounds,
            &[
                gx,
                f_error,
                big_b2,
                small2_times_absdiff,
                hbg_x,
                f_error_bound,
            ],
        );
        // le (abs term2) (mul big_b2 (mul small2 abs_diff))

        let assoc_eq2 = d.lemma(p.mul_assoc, &[big_b2, small2, abs_diff]);
        let mul_bigb2_small2 = cmul(d, p, big_b2, small2);
        let regroup2 = cmul(d, p, mul_bigb2_small2, abs_diff);
        let big_b2_small2_ad = cmul(d, p, big_b2, small2_times_absdiff);
        let assoc_symm2 = esymm(d, p, regroup2, big_b2_small2_ad, assoc_eq2);

        let (big_expr2, small_expr2, ofr_out2, fold_proof2) =
            fold_index0_first(d, p, k2, three_e, e2p);
        let refl_absdiff_b = erefl(d, p, abs_diff);
        let mul_bigexpr2_smallexpr2 = cmul(d, p, big_expr2, small_expr2);
        let mul_congr2 = d.lemma(
            p.mul_congr,
            &[
                mul_bigexpr2_smallexpr2,
                ofr_out2,
                abs_diff,
                abs_diff,
                fold_proof2,
                refl_absdiff_b,
            ],
        );
        let out_bound2 = cmul(d, p, ofr_out2, abs_diff);
        let bound_equiv2 = echain(
            d,
            p,
            big_b2_small2_ad,
            &[(regroup2, assoc_symm2), (out_bound2, mul_congr2)],
        );

        let abs_term2 = cabs(d, p, term2);
        let refl_abs_term2 = erefl(d, p, abs_term2);
        let term2_bound = d.lemma(
            p.le_congr,
            &[
                abs_term2,
                abs_term2,
                big_b2_small2_ad,
                out_bound2,
                refl_abs_term2,
                bound_equiv2,
                term2_upper,
            ],
        );
        // le (abs term2) out_bound2

        // --- term3 = (F(y)-F(x)) * G'(x) * (y-x) ------------------------------
        let fy_fx = cdiff(d, p, fy, fx);
        let uc_bound = d.lemma(
            p.uc_spec,
            &[f, a, b, huc, e3, y, x, hay, hyb, hax, hxb, h_c],
        );
        // le (abs fy_fx) (ofRat (natDivSucc 1 e3))
        let hbgp_x = d.apply(hbgp, &[x, hax, hxb]); // le (abs gpx) (mag_bound k3)
        let big_b3 = mag_bound(d, p, k3);
        let small3 = {
            let r = div_succ(d, p, 1, e3);
            d.const_app(p.of_rat, &[r])
        };

        let step3a = d.lemma(
            p.abs_mul_le_of_bounds,
            &[fy_fx, gpx, small3, big_b3, uc_bound, hbgp_x],
        );
        // le (abs (mul fy_fx gpx)) (mul small3 big_b3)

        let (small_expr3, big_expr3, ofr_out3, fold_proof3) =
            fold_index0_second(d, p, k3, three_e, e3);
        let mul_fyfx_gpx = cmul(d, p, fy_fx, gpx);
        let abs_mul_fyfx_gpx = cabs(d, p, mul_fyfx_gpx);
        let refl_abs_mfg = erefl(d, p, abs_mul_fyfx_gpx);
        let mul_smallexpr3_bigexpr3 = cmul(d, p, small_expr3, big_expr3);
        let step3b = d.lemma(
            p.le_congr,
            &[
                abs_mul_fyfx_gpx,
                abs_mul_fyfx_gpx,
                mul_smallexpr3_bigexpr3,
                ofr_out3,
                refl_abs_mfg,
                fold_proof3,
                step3a,
            ],
        );
        // le (abs (mul fy_fx gpx)) ofr_out3

        let le_refl_absdiff = d.lemma(p.le_refl, &[abs_diff]);
        let (term3, hi_term3, lo_term3, proof3) = expand_term3(d, p, fy, fx, gpx, diff_yx);
        let term3_bound = d.lemma(
            p.abs_mul_le_of_bounds,
            &[
                mul_fyfx_gpx,
                diff_yx,
                ofr_out3,
                abs_diff,
                step3b,
                le_refl_absdiff,
            ],
        );
        // le (abs term3) (mul ofr_out3 abs_diff)
        let out_bound3 = cmul(d, p, ofr_out3, abs_diff);
        let abs_term3 = cabs(d, p, term3);

        // --- combine the three bounds via the (3-way) triangle inequality ---
        let term1_plus_term2 = cadd(d, p, term1, term2);
        let combined_terms = cadd(d, p, term1_plus_term2, term3);

        let triangle_12 = abs_add_le(d, p, term1, term2);
        // le (abs term1_plus_term2) (add abs_term1 abs_term2)
        let sum12_le = d.lemma(
            p.add_le_add,
            &[
                abs_term1,
                out_bound1,
                abs_term2,
                out_bound2,
                term1_bound,
                term2_bound,
            ],
        );
        // le (add abs_term1 abs_term2) (add out_bound1 out_bound2)
        let abs_term1_plus_abs_term2 = cadd(d, p, abs_term1, abs_term2);
        let out_bound1_plus_out_bound2 = cadd(d, p, out_bound1, out_bound2);
        let abs_term1_plus_term2 = cabs(d, p, term1_plus_term2);
        let sum_ab_le = d.lemma(
            p.le_trans,
            &[
                abs_term1_plus_term2,
                abs_term1_plus_abs_term2,
                out_bound1_plus_out_bound2,
                triangle_12,
                sum12_le,
            ],
        );
        // le (abs term1_plus_term2) (add out_bound1 out_bound2)

        let triangle_123 = abs_add_le(d, p, term1_plus_term2, term3);
        // le (abs combined_terms) (add abs_term1_plus_term2 abs_term3)
        let sum123_le = d.lemma(
            p.add_le_add,
            &[
                abs_term1_plus_term2,
                out_bound1_plus_out_bound2,
                abs_term3,
                out_bound3,
                sum_ab_le,
                term3_bound,
            ],
        );
        // le (add abs_term1_plus_term2 abs_term3) (add out_bound1_plus_out_bound2 out_bound3)
        let abs_t1t2_plus_abs_t3 = cadd(d, p, abs_term1_plus_term2, abs_term3);
        let ob12_plus_ob3 = cadd(d, p, out_bound1_plus_out_bound2, out_bound3);
        let abs_combined = cabs(d, p, combined_terms);
        let combined_le = d.lemma(
            p.le_trans,
            &[
                abs_combined,
                abs_t1t2_plus_abs_t3,
                ob12_plus_ob3,
                triangle_123,
                sum123_le,
            ],
        );
        // le (abs combined_terms) ob12_plus_ob3

        // --- fuse the three equal `1/(3e+3)` shares down to `1/(e+1)` -------
        let r1 = div_succ(d, p, 1, three_e);
        let r2 = div_succ(d, p, 1, three_e);
        let r3 = div_succ(d, p, 1, three_e);
        let (final_out_bound, fuse_proof) = fuse_three_equal_bounds(
            d, p, e, three_e, ofr_out1, ofr_out2, ofr_out3, r1, r2, r3, abs_diff,
        );
        // Equiv ob12_plus_ob3 final_out_bound  [fuse_proof's actual shape:
        // Equiv (add (add (mul ofr_out1 abs_diff)(mul ofr_out2 abs_diff))(mul
        // ofr_out3 abs_diff)) final_out_bound -- structurally ob12_plus_ob3]

        let refl_abs_combined = erefl(d, p, abs_combined);
        let final_error_bound = d.lemma(
            p.le_congr,
            &[
                abs_combined,
                abs_combined,
                ob12_plus_ob3,
                final_out_bound,
                refl_abs_combined,
                fuse_proof,
                combined_le,
            ],
        );
        // le (abs combined_terms) final_out_bound

        // ==================================================================
        // The ring identity: `combined_terms ~ actual_error`, exactly. See
        // the module documentation's algebraic verification. `A := F(y)G(y)`,
        // `B := F(x)G(x)`, `C_raw/D_raw := F'(x)G(x)/F(x)G'(x)` (no `(y-x)`
        // factor yet -- that is what `fmul_p`'s own `mul _ diff_yx` supplies),
        // `E := F(y)G(x)`, `Gval := G(x)F(y)` (E's mirror, cancels against it
        // up to `mul_comm`), `B' := G(x)F(x)` (B's mirror, likewise).
        // ==================================================================
        let cap_a = cmul(d, p, fy, gy);
        let cap_b = cmul(d, p, fx, gx);
        let c_raw = cmul(d, p, fpx, gx);
        let d_raw = cmul(d, p, fx, gpx);
        let cap_e = cmul(d, p, fy, gx);
        let cap_gval = cmul(d, p, gx, fy);
        let cap_bp = cmul(d, p, gx, fx);

        // --- actual_error, mirroring `deriv_spec_body`'s own recipe with
        // `F := fmul, F' := fmul_p` -----------------------------------------
        let fmul_p_x = cadd(d, p, c_raw, d_raw);
        let deriv_term_mul = cmul(d, p, fmul_p_x, diff_yx);
        let a_minus_b = {
            let neg_b = cneg(d, p, cap_b);
            cadd(d, p, cap_a, neg_b)
        };
        let neg_deriv_term_mul = cneg(d, p, deriv_term_mul);
        let actual_error = cadd(d, p, a_minus_b, neg_deriv_term_mul);

        // deriv_term_mul ~ add c_full d_full, c_full/d_full carrying the
        // `(y-x)` factor `expand_term3`'s own `hi_term`/`lo_term` do too.
        let rd_cd = right_distrib(d, p, c_raw, d_raw, diff_yx);
        // Equiv deriv_term_mul (add c_full d_full)
        let c_full = cmul(d, p, c_raw, diff_yx);
        let d_full = cmul(d, p, d_raw, diff_yx);
        let neg_add_cd = cadd(d, p, c_full, d_full);
        let neg_congr_cd = d.lemma(p.neg_congr, &[deriv_term_mul, neg_add_cd, rd_cd]);
        // Equiv neg_deriv_term_mul (neg neg_add_cd)
        let neg_cd = neg_add_distrib(d, p, c_full, d_full);
        // Equiv (neg neg_add_cd) (add (neg c_full) (neg d_full))
        let neg_c_full = cneg(d, p, c_full);
        let neg_d_full = cneg(d, p, d_full);
        let neg_c_neg_d = cadd(d, p, neg_c_full, neg_d_full);
        let neg_neg_add_cd = cneg(d, p, neg_add_cd);
        let neg_deriv_chain = echain(
            d,
            p,
            neg_deriv_term_mul,
            &[(neg_neg_add_cd, neg_congr_cd), (neg_c_neg_d, neg_cd)],
        );
        // Equiv neg_deriv_term_mul neg_c_neg_d

        let refl_a_minus_b = erefl(d, p, a_minus_b);
        let ae_congr = d.lemma(
            p.add_congr,
            &[
                a_minus_b,
                a_minus_b,
                neg_deriv_term_mul,
                neg_c_neg_d,
                refl_a_minus_b,
                neg_deriv_chain,
            ],
        );
        let ae1 = cadd(d, p, a_minus_b, neg_c_neg_d);
        // Equiv actual_error ae1 = (A+negB) + (negC_full + negD_full)

        // --- reorder (term1+term2)+term3 into (term1+term3)+term2 -----------
        let term2_plus_term3 = cadd(d, p, term2, term3);
        let term1_plus_t2t3 = cadd(d, p, term1, term2_plus_term3);
        let reorder_step1 = d.lemma(p.add_assoc, &[term1, term2, term3]);
        // Equiv combined_terms term1_plus_t2t3
        let term3_plus_term2 = cadd(d, p, term3, term2);
        let term1_plus_t3t2 = cadd(d, p, term1, term3_plus_term2);
        let comm_23 = d.lemma(p.add_comm, &[term2, term3]);
        let refl_term1 = erefl(d, p, term1);
        let reorder_step2 = d.lemma(
            p.add_congr,
            &[
                term1,
                term1,
                term2_plus_term3,
                term3_plus_term2,
                refl_term1,
                comm_23,
            ],
        );
        // Equiv term1_plus_t2t3 term1_plus_t3t2
        let term1_plus_term3 = cadd(d, p, term1, term3);
        let t1t3_plus_term2 = cadd(d, p, term1_plus_term3, term2);
        let reorder_step3 = d.lemma(p.add_assoc, &[term1, term3, term2]);
        // Equiv t1t3_plus_term2 term1_plus_t3t2
        let reorder_step3_symm = esymm(d, p, t1t3_plus_term2, term1_plus_t3t2, reorder_step3);
        let reorder_proof = echain(
            d,
            p,
            combined_terms,
            &[
                (term1_plus_t2t3, reorder_step1),
                (term1_plus_t3t2, reorder_step2),
                (t1t3_plus_term2, reorder_step3_symm),
            ],
        );
        // Equiv combined_terms t1t3_plus_term2

        // --- congr: term1~target1, term3~term3exp, term2~target2 ------------
        let neg_lo_term3 = cneg(d, p, lo_term3);
        let term3exp = cadd(d, p, hi_term3, neg_lo_term3);
        let inner_congr = d.lemma(
            p.add_congr,
            &[term1, target1, term3, term3exp, proof1, proof3],
        );
        // Equiv term1_plus_term3 (add target1 term3exp)
        let target1_plus_term3exp = cadd(d, p, target1, term3exp);
        let outer_congr = d.lemma(
            p.add_congr,
            &[
                term1_plus_term3,
                target1_plus_term3exp,
                term2,
                target2,
                inner_congr,
                proof2,
            ],
        );
        // Equiv t1t3_plus_term2 (add target1_plus_term3exp target2)
        let target1t3exp_plus_target2 = cadd(d, p, target1_plus_term3exp, target2);

        // --- cancel_middle on (target1 + term3exp): the shared `f_term1`
        // piece (`target1`'s trailing `neg f_term1`, `term3exp`'s leading
        // `hi_term3`) cancels -- `hi_term3`/`lo_term3` are `expand_term3`'s
        // own copies, structurally identical to `f_term1`/`d_full` (both
        // `mul (mul (F y) (G' x)) (y-x)` / `mul (mul (F x) (G' x)) (y-x)`).
        let neg_e = cneg(d, p, cap_e);
        let cap_w = cadd(d, p, cap_a, neg_e);
        let cm_proof = cancel_middle(d, p, cap_w, f_term1, d_full);
        // Equiv (add (add cap_w (neg f_term1)) (add f_term1 (neg d_full))) (add cap_w (neg d_full))
        let w_minus_d = cadd(d, p, cap_w, neg_d_full);
        let refl_target2 = erefl(d, p, target2);
        let cm_congr = d.lemma(
            p.add_congr,
            &[
                target1_plus_term3exp,
                w_minus_d,
                target2,
                target2,
                cm_proof,
                refl_target2,
            ],
        );
        // Equiv target1t3exp_plus_target2 (add w_minus_d target2)
        let w_minus_d_plus_target2 = cadd(d, p, w_minus_d, target2);

        // --- the remaining six-leaf shuffle: (A-E-D) + ((Gval-B')-Hterm) ~
        // (A-B) + (-C-D), cancelling `neg_e + cap_gval ~ zero` (via
        // `mul_comm`) after bringing them adjacent, then `mul_comm`-ing
        // `cap_bp ~ cap_b` and `g_term2 ~ c_full` into place. ------------------
        let neg_bp = cneg(d, p, cap_bp);
        let neg_hterm = cneg(d, p, g_term2);
        let rest = cadd(d, p, neg_bp, neg_hterm);

        // 8a/8b: flatten both 3-term blocks.
        let assoc_p0 = d.lemma(p.add_assoc, &[cap_a, neg_e, neg_d_full]);
        let ne_plus_ndf = cadd(d, p, neg_e, neg_d_full);
        let p0_flat = cadd(d, p, cap_a, ne_plus_ndf);
        let assoc_q0 = d.lemma(p.add_assoc, &[cap_gval, neg_bp, neg_hterm]);
        let q0_flat = cadd(d, p, cap_gval, rest);

        // 8c: combine.
        let step_8c = d.lemma(
            p.add_congr,
            &[w_minus_d, p0_flat, target2, q0_flat, assoc_p0, assoc_q0],
        );
        let p0flat_plus_q0flat = cadd(d, p, p0_flat, q0_flat);

        // 8d: merge chains.
        let assoc_8d = d.lemma(p.add_assoc, &[cap_a, ne_plus_ndf, q0_flat]);
        let ne_ndf_plus_q0flat = cadd(d, p, ne_plus_ndf, q0_flat);
        let step_8d_result = cadd(d, p, cap_a, ne_ndf_plus_q0flat);

        // 8e: expose `neg_d_full + q0_flat`.
        let assoc_8e_local = d.lemma(p.add_assoc, &[neg_e, neg_d_full, q0_flat]);
        let ndf_plus_q0flat = cadd(d, p, neg_d_full, q0_flat);
        let ne_plus_that = cadd(d, p, neg_e, ndf_plus_q0flat);
        let refl_cap_a_e = erefl(d, p, cap_a);
        let step_8e = d.lemma(
            p.add_congr,
            &[
                cap_a,
                cap_a,
                ne_ndf_plus_q0flat,
                ne_plus_that,
                refl_cap_a_e,
                assoc_8e_local,
            ],
        );
        let step_8e_result = cadd(d, p, cap_a, ne_plus_that);

        // 8f: local swap of `neg_d_full` and `cap_gval` inside `ndf_plus_q0flat`.
        let assoc_rev_f_raw = d.lemma(p.add_assoc, &[neg_d_full, cap_gval, rest]);
        let ndf_plus_gval = cadd(d, p, neg_d_full, cap_gval);
        let ndf_gval_plus_rest = cadd(d, p, ndf_plus_gval, rest);
        let assoc_rev_f = esymm(d, p, ndf_gval_plus_rest, ndf_plus_q0flat, assoc_rev_f_raw);
        let comm_f = d.lemma(p.add_comm, &[neg_d_full, cap_gval]);
        let gval_plus_ndf = cadd(d, p, cap_gval, neg_d_full);
        let refl_rest_f = erefl(d, p, rest);
        let congr_f = d.lemma(
            p.add_congr,
            &[
                ndf_plus_gval,
                gval_plus_ndf,
                rest,
                rest,
                comm_f,
                refl_rest_f,
            ],
        );
        let gval_ndf_plus_rest = cadd(d, p, gval_plus_ndf, rest);
        let assoc_fwd_f = d.lemma(p.add_assoc, &[cap_gval, neg_d_full, rest]);
        let ndf_plus_rest = cadd(d, p, neg_d_full, rest);
        let gval_plus_that = cadd(d, p, cap_gval, ndf_plus_rest);
        let swap_f = echain(
            d,
            p,
            ndf_plus_q0flat,
            &[
                (ndf_gval_plus_rest, assoc_rev_f),
                (gval_ndf_plus_rest, congr_f),
                (gval_plus_that, assoc_fwd_f),
            ],
        );
        // Equiv ndf_plus_q0flat gval_plus_that

        let refl_neg_e = erefl(d, p, neg_e);
        let lift1_f = d.lemma(
            p.add_congr,
            &[
                neg_e,
                neg_e,
                ndf_plus_q0flat,
                gval_plus_that,
                refl_neg_e,
                swap_f,
            ],
        );
        let ne_plus_gvalthat = cadd(d, p, neg_e, gval_plus_that);
        let refl_cap_a_f = erefl(d, p, cap_a);
        let lift2_f = d.lemma(
            p.add_congr,
            &[
                cap_a,
                cap_a,
                ne_plus_that,
                ne_plus_gvalthat,
                refl_cap_a_f,
                lift1_f,
            ],
        );
        let step_f_result = cadd(d, p, cap_a, ne_plus_gvalthat);

        // 8g: expose `neg_e + cap_gval`.
        let assoc_rev_g_raw = d.lemma(p.add_assoc, &[neg_e, cap_gval, ndf_plus_rest]);
        let ne_gval_plus_rest = cadd(d, p, neg_e, cap_gval);
        let ne_gval_plus_ndfrest = cadd(d, p, ne_gval_plus_rest, ndf_plus_rest);
        let assoc_rev_g = esymm(
            d,
            p,
            ne_gval_plus_ndfrest,
            ne_plus_gvalthat,
            assoc_rev_g_raw,
        );
        let refl_cap_a_g = erefl(d, p, cap_a);
        let lift_g = d.lemma(
            p.add_congr,
            &[
                cap_a,
                cap_a,
                ne_plus_gvalthat,
                ne_gval_plus_ndfrest,
                refl_cap_a_g,
                assoc_rev_g,
            ],
        );
        let step_g_result = cadd(d, p, cap_a, ne_gval_plus_ndfrest);

        // 8h: `neg_e + cap_gval ~ zero`, via `Gval ~ E` (`mul_comm`).
        let comm_ge = d.lemma(p.mul_comm, &[gx, fy]); // Equiv cap_gval cap_e
        let refl_neg_e_h = erefl(d, p, neg_e);
        let congr_h1 = d.lemma(
            p.add_congr,
            &[neg_e, neg_e, cap_gval, cap_e, refl_neg_e_h, comm_ge],
        );
        let ne_plus_e = cadd(d, p, neg_e, cap_e);
        let comm_h2 = d.lemma(p.add_comm, &[neg_e, cap_e]);
        let e_plus_ne = cadd(d, p, cap_e, neg_e);
        let addneg_h3 = d.lemma(p.add_neg, &[cap_e]);
        let zero_c = czero(d, p);
        let cancel_h = echain(
            d,
            p,
            ne_gval_plus_rest,
            &[
                (ne_plus_e, congr_h1),
                (e_plus_ne, comm_h2),
                (zero_c, addneg_h3),
            ],
        );
        // Equiv ne_gval_plus_rest zero_c

        // 8i: collapse the resulting `zero + rest`.
        let refl_ndfrest = erefl(d, p, ndf_plus_rest);
        let congr_i1 = d.lemma(
            p.add_congr,
            &[
                ne_gval_plus_rest,
                zero_c,
                ndf_plus_rest,
                ndf_plus_rest,
                cancel_h,
                refl_ndfrest,
            ],
        );
        let zero_plus_ndfrest = cadd(d, p, zero_c, ndf_plus_rest);
        let comm_i2 = d.lemma(p.add_comm, &[zero_c, ndf_plus_rest]);
        let ndfrest_plus_zero = cadd(d, p, ndf_plus_rest, zero_c);
        let addzero_i3 = d.lemma(p.add_zero, &[ndf_plus_rest]);
        let chain_i = echain(
            d,
            p,
            ne_gval_plus_ndfrest,
            &[
                (zero_plus_ndfrest, congr_i1),
                (ndfrest_plus_zero, comm_i2),
                (ndf_plus_rest, addzero_i3),
            ],
        );
        // Equiv ne_gval_plus_ndfrest ndf_plus_rest

        let refl_cap_a_i = erefl(d, p, cap_a);
        let lift_i = d.lemma(
            p.add_congr,
            &[
                cap_a,
                cap_a,
                ne_gval_plus_ndfrest,
                ndf_plus_rest,
                refl_cap_a_i,
                chain_i,
            ],
        );
        let step_i_result = cadd(d, p, cap_a, ndf_plus_rest);

        // 8j: expose `(cap_a + neg_d_full)`.
        let assoc_j_raw = d.lemma(p.add_assoc, &[cap_a, neg_d_full, rest]);
        let a_plus_ndf = cadd(d, p, cap_a, neg_d_full);
        let a_ndf_plus_rest = cadd(d, p, a_plus_ndf, rest);
        let assoc_rev_j = esymm(d, p, a_ndf_plus_rest, step_i_result, assoc_j_raw);

        // 8k: `add4_comm` -- swap `neg_d_full` and `neg_bp`.
        let (step_k_result, add4_proof) = add4_comm(d, p, cap_a, neg_d_full, neg_bp, neg_hterm);
        // step_k_result = (cap_a+neg_bp)+(neg_d_full+neg_hterm)

        // 8l: commute the second block.
        let comm_l = d.lemma(p.add_comm, &[neg_d_full, neg_hterm]);
        let a_plus_negbp = cadd(d, p, cap_a, neg_bp);
        let ndf_plus_nhterm = cadd(d, p, neg_d_full, neg_hterm);
        let nhterm_plus_ndf = cadd(d, p, neg_hterm, neg_d_full);
        let refl_a_negbp = erefl(d, p, a_plus_negbp);
        let lift_l = d.lemma(
            p.add_congr,
            &[
                a_plus_negbp,
                a_plus_negbp,
                ndf_plus_nhterm,
                nhterm_plus_ndf,
                refl_a_negbp,
                comm_l,
            ],
        );
        let step_l_result = cadd(d, p, a_plus_negbp, nhterm_plus_ndf);

        // 8m: `neg_bp ~ neg_cap_b` and `neg_hterm ~ neg_c_full` (both `mul_comm`).
        let comm_bp = d.lemma(p.mul_comm, &[gx, fx]); // Equiv cap_bp cap_b
        let neg_cap_b = cneg(d, p, cap_b);
        let neg_congr_bp = d.lemma(p.neg_congr, &[cap_bp, cap_b, comm_bp]); // Equiv neg_bp neg_cap_b

        let comm_hterm_inner = d.lemma(p.mul_comm, &[gx, fpx]); // Equiv (mul gx fpx) (mul fpx gx)
        let refl_diff_m = erefl(d, p, diff_yx);
        let mul_gxfpx = cmul(d, p, gx, fpx);
        let mul_fpxgx = cmul(d, p, fpx, gx);
        let congr_hterm_outer = d.lemma(
            p.mul_congr,
            &[
                mul_gxfpx,
                mul_fpxgx,
                diff_yx,
                diff_yx,
                comm_hterm_inner,
                refl_diff_m,
            ],
        ); // Equiv g_term2 c_full
        let neg_congr_hterm = d.lemma(p.neg_congr, &[g_term2, c_full, congr_hterm_outer]);
        // Equiv neg_hterm neg_c_full

        let refl_cap_a_m = erefl(d, p, cap_a);
        let final_congr_bp = d.lemma(
            p.add_congr,
            &[cap_a, cap_a, neg_bp, neg_cap_b, refl_cap_a_m, neg_congr_bp],
        );
        // Equiv a_plus_negbp (add cap_a neg_cap_b)
        let a_plus_negcapb = cadd(d, p, cap_a, neg_cap_b);
        let refl_neg_d_full = erefl(d, p, neg_d_full);
        let final_congr_pair = d.lemma(
            p.add_congr,
            &[
                neg_hterm,
                neg_c_full,
                neg_d_full,
                neg_d_full,
                neg_congr_hterm,
                refl_neg_d_full,
            ],
        );
        // Equiv nhterm_plus_ndf (add neg_c_full neg_d_full)
        let final_congr = d.lemma(
            p.add_congr,
            &[
                a_plus_negbp,
                a_plus_negcapb,
                nhterm_plus_ndf,
                neg_c_neg_d,
                final_congr_bp,
                final_congr_pair,
            ],
        );
        // Equiv step_l_result (add a_plus_negcapb neg_c_neg_d)
        let final_target = cadd(d, p, a_plus_negcapb, neg_c_neg_d);
        // `final_target` is defeq to `ae1` (`a_minus_b` is `add cap_a neg_cap_b`
        // built the same way, just independently, inside its own block above).

        // --- assemble the whole shuffle: w_minus_d_plus_target2 ~ final_target
        let shuffle_proof = echain(
            d,
            p,
            w_minus_d_plus_target2,
            &[
                (p0flat_plus_q0flat, step_8c),
                (step_8d_result, assoc_8d),
                (step_8e_result, step_8e),
                (step_f_result, lift2_f),
                (step_g_result, lift_g),
                (step_i_result, lift_i),
                (a_ndf_plus_rest, assoc_rev_j),
                (step_k_result, add4_proof),
                (step_l_result, lift_l),
                (final_target, final_congr),
            ],
        );
        // Equiv w_minus_d_plus_target2 final_target (~ ae1)

        // --- assemble the whole ring identity ---------------------------------
        let ring_chain = echain(
            d,
            p,
            combined_terms,
            &[
                (t1t3_plus_term2, reorder_proof),
                (target1t3exp_plus_target2, outer_congr),
                (w_minus_d_plus_target2, cm_congr),
                (final_target, shuffle_proof),
            ],
        );
        // Equiv combined_terms final_target
        let ae1_symm = esymm(d, p, actual_error, ae1, ae_congr);
        // Equiv ae1 actual_error (final_target is defeq to ae1)
        let full_ring_proof = d.lemma(
            p.equiv_trans,
            &[
                combined_terms,
                final_target,
                actual_error,
                ring_chain,
                ae1_symm,
            ],
        );
        // Equiv combined_terms actual_error
        let full_ring_proof_rev = esymm(d, p, combined_terms, actual_error, full_ring_proof);
        // Equiv actual_error combined_terms

        let conclusion = abs_le_of_equiv(
            d,
            p,
            actual_error,
            combined_terms,
            final_out_bound,
            full_ring_proof_rev,
            final_error_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[fmul, fmul_p, a, b, modulus_mul, spec]);
    let value = {
        let with_hbgp = d.lam_fv(hbgp_fv, hbgp_ty, mk_applied);
        let with_hbg = d.lam_fv(hbg_fv, hbg_ty, with_hbgp);
        let with_hbf = d.lam_fv(hbf_fv, hbf_ty, with_hbg);
        let with_k3 = d.lam_fv(k3_fv, nat, with_hbf);
        let with_k2 = d.lam_fv(k2_fv, nat, with_k3);
        let with_k1 = d.lam_fv(k1_fv, nat, with_k2);
        let with_huc = d.lam_fv(huc_fv, huc_ty, with_k1);
        let with_hg = d.lam_fv(hg_fv, hg_ty, with_huc);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hg);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_gp = d.lam_fv(gp_fv, func_ty, with_a);
        let with_g = d.lam_fv(g_fv, func_ty, with_gp);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_g);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, fmul, fmul_p, a, b);
        let with_hbgp = d.arrow(hbgp_ty, applied);
        let with_hbg = d.arrow(hbg_ty, with_hbgp);
        let with_hbf = d.arrow(hbf_ty, with_hbg);
        let with_k3 = d.pi_fv(k3_fv, nat, with_hbf);
        let with_k2 = d.pi_fv(k2_fv, nat, with_k3);
        let with_k1 = d.pi_fv(k1_fv, nat, with_k2);
        let with_huc = d.arrow(huc_ty, with_k1);
        let with_hg = d.arrow(hg_ty, with_huc);
        let with_hf = d.arrow(hf_ty, with_hg);
        let with_b = d.pi_fv(b_fv, carrier, with_hf);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_gp = d.pi_fv(gp_fv, func_ty, with_a);
        let with_g = d.pi_fv(g_fv, func_ty, with_gp);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_g);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.hasDerivative_cube : ∀ a b k1 k2 k3, ... → HasDerivativeOn (fun r
/// => mul r (mul r r)) (fun x => add (mul one (mul x x)) (mul x (add x
/// x))) a b` — see [`CRealPrelude::has_derivative_cube`]'s own doc comment
/// for the statement in full and why the three magnitude bounds are kept
/// independent rather than folded into one.
///
/// Built with **zero new algebra**: `r*(r*r)` is literally `id(r) * sq(r)`,
/// so the whole proof is [`declare_has_derivative_mul`]'s own theorem
/// applied to [`CRealPrelude::has_derivative_id`] and
/// [`CRealPrelude::has_derivative_sq`], with
/// [`CRealPrelude::uniformly_continuous_id`] supplying the continuity
/// hypothesis `hasDerivative_mul`'s own third term needs — no ring identity
/// is derived here at all, unlike `hasDerivative_sq`'s `diff_of_squares`
/// route.
fn declare_has_derivative_cube(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    // Rebuilt locally rather than imported: `declare_has_derivative_id` and
    // `declare_has_derivative_sq` each build their own `identity`/`square`
    // terms as PRIVATE locals, exactly the way `declare_has_derivative_pow_two`
    // already rebuilds `sq_fn`/`sq_deriv` locally before calling
    // `p.has_derivative_sq` — a fresh `fun r => r` (resp. `fun r => r*r`)
    // built here is the SAME final term after `lam_fv` abstraction erases the
    // scaffolding free variable, so this matches the type `p.has_derivative_id`
    // (resp. `p.has_derivative_sq`) actually carries.
    let id_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let one_fn = {
        let ignore_fv = d.fresh_fvar();
        let one_c = d.kernel().const_(p.one, vec![]);
        d.lam_fv(ignore_fv, carrier, one_c)
    };
    let sq_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let rr = cmul(d, p, r, r);
        d.lam_fv(r_fv, carrier, rr)
    };
    let double_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let xx = cadd(d, p, x, x);
        d.lam_fv(x_fv, carrier, xx)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);
    let k3_fv = d.fresh_fvar();
    let k3 = d.kernel().fvar(k3_fv);

    // Same `bounded_on_ty` shape `declare_has_derivative_mul` itself uses for
    // its own `hbf`/`hbg`/`hbgp`, applied at `id_fn`/`sq_fn`/`double_fn` so
    // the types line up with `p.has_derivative_mul`'s own hypothesis types
    // exactly (not merely up to a defeq the application would still have to
    // re-derive).
    let hbf_ty = bounded_on_ty(d, p, id_fn, a, b, k1);
    let hbf_fv = d.fresh_fvar();
    let hbf = d.kernel().fvar(hbf_fv);
    let hbg_ty = bounded_on_ty(d, p, sq_fn, a, b, k2);
    let hbg_fv = d.fresh_fvar();
    let hbg = d.kernel().fvar(hbg_fv);
    let hbgp_ty = bounded_on_ty(d, p, double_fn, a, b, k3);
    let hbgp_fv = d.fresh_fvar();
    let hbgp = d.kernel().fvar(hbgp_fv);

    let hf = d.const_app(p.has_derivative_id, &[a, b]);
    let hg = d.const_app(p.has_derivative_sq, &[a, b]);
    let huc = d.const_app(p.uniformly_continuous_id, &[a, b]);

    let mk_applied = d.const_app(
        p.has_derivative_mul,
        &[
            id_fn, one_fn, sq_fn, double_fn, a, b, hf, hg, huc, k1, k2, k3, hbf, hbg, hbgp,
        ],
    );

    let value = {
        let with_hbgp = d.lam_fv(hbgp_fv, hbgp_ty, mk_applied);
        let with_hbg = d.lam_fv(hbg_fv, hbg_ty, with_hbgp);
        let with_hbf = d.lam_fv(hbf_fv, hbf_ty, with_hbg);
        let with_k3 = d.lam_fv(k3_fv, nat, with_hbf);
        let with_k2 = d.lam_fv(k2_fv, nat, with_k3);
        let with_k1 = d.lam_fv(k1_fv, nat, with_k2);
        let with_b = d.lam_fv(b_fv, carrier, with_k1);
        d.lam_fv(a_fv, carrier, with_b)
    };

    // Stated with the plain, unfolded `r*(r*r)` / `1*(x*x) + x*(x+x)` shape
    // rather than `id_fn`/`sq_fn` applied — defeq to `mk_applied`'s own
    // inferred type by beta reduction alone (`Kernel::add_declaration` checks
    // the value's type against this one up to definitional equality, the same
    // way `declare_has_derivative_pow_two` states its `ty` using `CReal.pow`
    // while its `value` is built through `hasDerivative_congr` entirely).
    let cube_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let rr = cmul(d, p, r, r);
        let rrr = cmul(d, p, r, rr);
        d.lam_fv(r_fv, carrier, rrr)
    };
    let cube_deriv = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let one_c = d.kernel().const_(p.one, vec![]);
        let xx = cmul(d, p, x, x);
        let one_xx = cmul(d, p, one_c, xx);
        let xpx = cadd(d, p, x, x);
        let x_xpx = cmul(d, p, x, xpx);
        let sum = cadd(d, p, one_xx, x_xpx);
        d.lam_fv(x_fv, carrier, sum)
    };

    let ty = {
        let applied = hd_ty(d, p, cube_fn, cube_deriv, a, b);
        let with_hbgp = d.arrow(hbgp_ty, applied);
        let with_hbg = d.arrow(hbg_ty, with_hbgp);
        let with_hbf = d.arrow(hbf_ty, with_hbg);
        let with_k3 = d.pi_fv(k3_fv, nat, with_hbf);
        let with_k2 = d.pi_fv(k2_fv, nat, with_k3);
        let with_k1 = d.pi_fv(k1_fv, nat, with_k2);
        let with_b = d.pi_fv(b_fv, carrier, with_k1);
        d.pi_fv(a_fv, carrier, with_b)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_cube,
        uparams: vec![],
        ty,
        value,
    })
}

/// `∀ x, le a x → le x b → Equiv (lhs x) (rhs x)` — the shape of both
/// agreement hypotheses [`declare_has_derivative_congr`] takes, built once
/// and reused for `G`/`F` and `G'`/`F'`.
fn agree_on_interval_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    lhs_fn: ExprId,
    rhs_fn: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let range_ax = d.const_app(p.le, &[a, x]);
    let range_xb = d.const_app(p.le, &[x, b]);
    let lx = d.apply(lhs_fn, &[x]);
    let rx = d.apply(rhs_fn, &[x]);
    let eq = d.const_app(p.equiv, &[lx, rx]);

    let with_hxb = d.arrow(range_xb, eq);
    let with_hax = d.arrow(range_ax, with_hxb);
    d.pi_fv(x_fv, carrier, with_hax)
}

/// `Equiv (pow x 2) (mul x x)` — `pow x 2` ι-reduces (`pow`'s own `Nat.rec`,
/// twice, then `pow_zero`'s base case) to `mul (mul one x) x`, definitionally
/// (this is exactly how [`super::power`]'s own induction steps rely on
/// `pow`'s ι-reduction rather than calling `pow_succ`/`pow_zero` as rewrite
/// lemmas — see e.g. `declare_pow_nonneg`). What is not definitional is
/// `mul one x ~ x`: closed by `mul_comm` then `mul_one`, then lifted through
/// `mul_congr` on the right factor `x` (reflexivity).
fn pow_two_equiv_sq(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let one_c = d.kernel().const_(p.one, vec![]);
    let mul_one_x = cmul(d, p, one_c, x);
    let mul_x_one = cmul(d, p, x, one_c);
    let comm = d.lemma(p.mul_comm, &[one_c, x]); // mul_one_x ~ mul_x_one
    let mo = d.lemma(p.mul_one, &[x]); // mul_x_one ~ x
    let one_x_eq_x = echain(d, p, mul_one_x, &[(mul_x_one, comm), (x, mo)]); // mul_one_x ~ x
    let refl_x = erefl(d, p, x);
    // Equiv (mul (mul one x) x) (mul x x) — defeq to Equiv (pow x 2) (mul x x).
    d.lemma(p.mul_congr, &[mul_one_x, x, x, x, one_x_eq_x, refl_x])
}

/// `CReal.hasDerivative_congr : ∀ F F' a b, HasDerivativeOn F F' a b →
/// ∀ G G', (∀ x, le a x → le x b → Equiv (G x) (F x)) →
/// (∀ x, le a x → le x b → Equiv (G' x) (F' x)) → HasDerivativeOn G G' a b`
///
/// **The hypothesis shape, decided from `HasDerivativeOn.spec`'s own
/// type, not assumed.** `spec`'s conclusion mentions `F x`, `F y`, `F' x`
/// only inside a body reached through `le a x → le x b → le a y → le y b →
/// …` — the SAME four range hypotheses a caller of `spec` must already hold
/// to reach that body at all. So agreement of `G`/`G'` with `F`/`F'` is only
/// ever exercised at a point already proved to lie in `[a,b]`, and
/// agreement OFF the interval is neither needed nor assumed here — the two
/// hypotheses above are exactly `∀ x ∈ [a,b], …`, nothing wider.
///
/// Reuses `F`'s own modulus **verbatim** (no rescaling: this is a pure
/// relabelling, not an estimate). The error term transports to `F`'s own
/// error term by two structural steps — `add_congr`/`neg_congr` for the
/// `G y − G x` half, `mul_congr`/`neg_congr` for the `G'(x)·(y−x)` half,
/// then one more `add_congr` to combine — and [`abs_le_of_equiv`] carries
/// `F`'s own bound (from `F`'s own `spec`, at the identical `e x y` and
/// range proofs) across that `Equiv`.
fn declare_has_derivative_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let gp_fv = d.fresh_fvar();
    let gp = d.kernel().fvar(gp_fv);

    let agree_g_ty = agree_on_interval_ty(d, p, a, b, g, f);
    let agree_gp_ty = agree_on_interval_ty(d, p, a, b, gp, fp);
    let agree_g_fv = d.fresh_fvar();
    let agree_g = d.kernel().fvar(agree_g_fv);
    let agree_gp_fv = d.fresh_fvar();
    let agree_gp = d.kernel().fvar(agree_gp_fv);

    // Reuse F's own modulus verbatim — this is a relabelling, not an
    // estimate, so no rescaling is needed.
    let modulus = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
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

        let diff_yx = cdiff(d, p, y, x);
        let abs_diff = cabs(d, p, diff_yx);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);

        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);
        let h_fv_expr = d.kernel().fvar(h_fv);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let deriv_term_f = cmul(d, p, fpx, diff_yx);
        let fy_fx_f = cdiff(d, p, fy, fx);
        let error_f = cdiff(d, p, fy_fx_f, deriv_term_f);

        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);
        let gpx = d.apply(gp, &[x]);
        let deriv_term_g = cmul(d, p, gpx, diff_yx);
        let gy_gx_g = cdiff(d, p, gy, gx);
        let error_g = cdiff(d, p, gy_gx_g, deriv_term_g);

        let out_bound_rat = div_succ(d, p, 1, e);
        let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);
        let out_bound = cmul(d, p, ofr_out, abs_diff);

        // gy ~ fy, gx ~ fx, gpx ~ fpx — the two agreement hypotheses,
        // instantiated at x (with x's own range proofs) and at y (with y's).
        let gy_eq_fy = d.apply(agree_g, &[y, hay, hyb]);
        let gx_eq_fx = d.apply(agree_g, &[x, hax, hxb]);
        let gpx_eq_fpx = d.apply(agree_gp, &[x, hax, hxb]);

        let neg_gx = cneg(d, p, gx);
        let neg_fx = cneg(d, p, fx);
        let neg_gx_eq_neg_fx = d.lemma(p.neg_congr, &[gx, fx, gx_eq_fx]);

        // gy_gx_g ~ fy_fx_f : Equiv (add gy (neg gx)) (add fy (neg fx))
        let gy_gx_eq_fy_fx = d.lemma(
            p.add_congr,
            &[gy, fy, neg_gx, neg_fx, gy_eq_fy, neg_gx_eq_neg_fx],
        );

        // deriv_term_g ~ deriv_term_f : Equiv (mul gpx diff) (mul fpx diff)
        let refl_diff = erefl(d, p, diff_yx);
        let deriv_term_eq = d.lemma(
            p.mul_congr,
            &[gpx, fpx, diff_yx, diff_yx, gpx_eq_fpx, refl_diff],
        );
        let neg_deriv_term_eq = d.lemma(p.neg_congr, &[deriv_term_g, deriv_term_f, deriv_term_eq]);

        // error_g ~ error_f.
        let neg_deriv_term_g = cneg(d, p, deriv_term_g);
        let neg_deriv_term_f = cneg(d, p, deriv_term_f);
        let error_g_eq_error_f = d.lemma(
            p.add_congr,
            &[
                gy_gx_g,
                fy_fx_f,
                neg_deriv_term_g,
                neg_deriv_term_f,
                gy_gx_eq_fy_fx,
                neg_deriv_term_eq,
            ],
        );

        let error_f_bound = d.lemma(
            p.hd_spec,
            &[f, fp, a, b, hf, e, x, y, hax, hxb, hay, hyb, h_fv_expr],
        ); // le (abs error_f) out_bound
        let conclusion = abs_le_of_equiv(
            d,
            p,
            error_g,
            error_f,
            out_bound,
            error_g_eq_error_f,
            error_f_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[g, gp, a, b, modulus, spec]);
    let value = {
        let with_agree_gp = d.lam_fv(agree_gp_fv, agree_gp_ty, mk_applied);
        let with_agree_g = d.lam_fv(agree_g_fv, agree_g_ty, with_agree_gp);
        let with_gp = d.lam_fv(gp_fv, func_ty, with_agree_g);
        let with_g = d.lam_fv(g_fv, func_ty, with_gp);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_g);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, g, gp, a, b);
        let with_agree_gp = d.arrow(agree_gp_ty, applied);
        let with_agree_g = d.arrow(agree_g_ty, with_agree_gp);
        let with_gp = d.pi_fv(gp_fv, func_ty, with_agree_g);
        let with_g = d.pi_fv(g_fv, func_ty, with_gp);
        let with_hf = d.arrow(hf_ty, with_g);
        let with_b = d.pi_fv(b_fv, carrier, with_hf);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.hasDerivative_pow_two : ∀ a b, HasDerivativeOn (fun r => pow r 2)
/// (fun x => add x x) a b` — [`declare_has_derivative_congr`] transporting
/// [`CRealPrelude::has_derivative_sq`]'s own witness across
/// [`pow_two_equiv_sq`]. `G' := F'` **verbatim** (the same `fun x => add x
/// x` term, not merely `Equiv`-equal to it), so the second agreement
/// hypothesis is closed by `Equiv.refl` alone — no transport needed on the
/// derivative side at all.
///
/// **The real cross-check** the module documentation for
/// [`declare_has_derivative_sq`] promises: if the general transport built
/// above did not compose with `hasDerivative_sq`'s own statement at this one
/// instance, one of the two would be wrong, and finding out which would be
/// worth more than this theorem.
pub(super) fn declare_has_derivative_pow_two(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let sq_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let rr = cmul(d, p, r, r);
        d.lam_fv(r_fv, carrier, rr)
    };
    let sq_deriv = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let xx = cadd(d, p, x, x);
        d.lam_fv(x_fv, carrier, xx)
    };
    let pow_two_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let two = d.num(2);
        let pr2 = d.const_app(p.pow, &[r, two]);
        d.lam_fv(r_fv, carrier, pr2)
    };

    let hf = d.const_app(p.has_derivative_sq, &[a, b]); // HasDerivativeOn sq_fn sq_deriv a b

    // agree_g : ∀ x, le a x → le x b → Equiv (pow x 2) (mul x x)
    let agree_g = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let eq = pow_two_equiv_sq(d, p, x);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, eq);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        d.lam_fv(x_fv, carrier, with_hax)
    };

    // agree_gp : ∀ x, le a x → le x b → Equiv (add x x) (add x x) — Equiv.refl.
    let agree_gp = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let xx = cadd(d, p, x, x);
        let refl = erefl(d, p, xx);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, refl);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        d.lam_fv(x_fv, carrier, with_hax)
    };

    let applied = d.const_app(
        p.has_derivative_congr,
        &[
            sq_fn, sq_deriv, a, b, hf, pow_two_fn, sq_deriv, agree_g, agree_gp,
        ],
    );

    let value = {
        let with_b = d.lam_fv(b_fv, carrier, applied);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let target = hd_ty(d, p, pow_two_fn, sq_deriv, a, b);
        let with_b = d.pi_fv(b_fv, carrier, target);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_pow_two,
        uparams: vec![],
        ty,
        value,
    })
}
