//! **Finite sums over the constructed reals**, `CReal.sumRange`, and the
//! first genuinely analytic facts about them (monotonicity, the triangle
//! inequality) — the missing floor under every series and every integral over
//! `CReal`.
//!
//! ## The convention, matched to `Nat`/`Complex`
//!
//! `CReal.sumRange` is structural `Nat.rec` on the bound, matching
//! `Nat.sumRange`'s own convention exactly
//! (`nat_prelude/defs.rs::declare_finite_ranges`) and `Complex.sumRange`'s
//! (`complex.rs::declare_sum_range`, landed the same day): `sumRange f zero ≡
//! zero`, `sumRange f (succ j) ≡ add (sumRange f j) (f j)` — recursion on the
//! bound, the new term folded on the **right** of the prior sum. This is the
//! fourth carrier to match this convention (`Int.pow`, `Complex.pow`,
//! `Int.prodRange`, `Complex.sumRange` all did before it); nothing here
//! invents a fifth.
//!
//! `sumRange_zero`/`sumRange_succ` close by `Eq.refl` alone, exactly as
//! `Complex.sumRange_zero`/`_succ` do: `sumRange`'s `Nat.rec` application
//! ι-reduces to the algebraic combinator (`zero`, or `add (sumRange f n) (f
//! n)`) directly, with no `CReal.add`/`CReal.neg` internals ever unfolded to
//! get there, so this is independent of `CReal`'s own carrier being a setoid.
//! Every other law here **does** need `Equiv`, never `Eq`: `CReal.Equiv` is a
//! defined `Prop` relation and nothing rewrites under a `sumRange` for free.
//!
//! ## What the analytic laws needed that did not already exist
//!
//! [`declare_sum_range_add`] needs the four-term rearrangement `(A+B)+(C+D) ~
//! (A+C)+(B+D)` — the `Equiv` promotion of
//! `nat_prelude/binomial.rs::add_add_add_comm` — built inline as
//! [`add4_comm`] rather than declared, exactly as the `Eq Nat` original is
//! only ever a proof-term helper, never a kernel theorem of its own.
//!
//! [`declare_abs_sum_range_le`] (the triangle inequality for a finite sum)
//! needed a two-term triangle inequality `abs_add_le` first, and *that*
//! needed `neg(add a b) ~ add(neg a)(neg b)` — a standard additive-inverse
//! law `CReal` has no standalone declaration for. [`neg_add`] derives it from
//! [`add4_comm`] and the additive-inverse laws (`add_neg`, `add_zero`,
//! `add_comm`, `add_assoc`) by the usual "any right inverse is the inverse"
//! argument, specialised to the one instance needed rather than proved as a
//! general uniqueness lemma. None of `add4_comm`/`neg_add`/`abs_add_le` are
//! declared kernel theorems — they are Rust-level proof-term builders, the
//! same status `add_add_add_comm` has for `Nat`.
//!
//! ## Telescoping, splitting, and the comparison test
//!
//! [`declare_sum_range_telescope`] and [`declare_sum_range_split`] are the
//! two facts every convergence argument over a series opens with — the first
//! collapses `Σ_{k<n} (f(k+1) − f k)` to `f n − f 0`, the second turns a
//! statement about a *tail* of a sum into a statement about a *difference*
//! of two partial sums. Both are induction on `n` closed by algebra alone
//! (no rational estimate): telescoping needs one more cancellation shape,
//! [`cancel_left`] (`(a+b)+(c+(−a)) ~ c+b`, four terms, via [`add4_comm`]),
//! and splitting needs only `Nat.add`'s own iota-reduction plus
//! `add_zero`/`add_assoc`.
//!
//! [`declare_sum_range_tail_le`] is the comparison test itself: `f`
//! pointwise-bounded by `g` in absolute value forces every tail of `f`'s
//! partial sums to be bounded by the corresponding tail of `g`'s. It is
//! **not** stated through `CReal.Cauchy` (`creal/convergence.rs`), and that
//! is a deliberate, considered choice, not an oversight. `CReal.Cauchy`'s
//! body — see that module's own documentation — compares `seq (h m) m`
//! against `seq (h n) n`: the *rational* sample each real offers at **its
//! own canonical index**, the same representative-level machinery
//! `completeness.rs`/`convergence.rs` build extensively for `CReal.add`'s
//! single shift. Reaching that shape for `h := sumRange f` needs a
//! sample-rate law for `sumRange` itself — how `seq (sumRange f n) k`
//! relates to the individual `f i`'s own samples — and every other
//! `sumRange` law in this file, [`declare_sum_range_tail_le`] included, is
//! proved through the abstract `Equiv`/`le`/`abs` algebra alone and never
//! once inspects `seq`. [`declare_sum_range_tail_le`] is the actual
//! mathematical engine of the comparison test — a genuine real-valued tail
//! bound, via [`declare_sum_range_split`] to rewrite each tail as a shifted
//! partial sum ([`cancel_right`]: `(a+b)+(−a) ~ b`), then
//! [`super::CRealPrelude::abs_sum_range_le`] and
//! [`super::CRealPrelude::sum_range_le`] to bound it.
//!
//! ## The sample-rate law itself: cheap in recursive form, not in closed form
//!
//! An earlier slice of this file reported the sample-rate law above as
//! "not existing anywhere in this development" and "plausibly a module the
//! size of `completeness.rs` on its own". The **recursive** form of the law
//! is not that expensive, and [`declare_sum_range_seq_equations`] proves it
//! outright:
//!
//! ```text
//! CReal.sumRange_seq_zero : ∀ f k, Eq Rat (seq (sumRange f Nat.zero) k) Rat.zero
//! CReal.sumRange_seq_succ : ∀ f n k, Eq Rat (seq (sumRange f (Nat.succ n)) k)
//!   (Rat.add (seq (sumRange f n) (shift k)) (seq (f n) (shift k)))
//! ```
//!
//! Both close by `Eq.refl` alone — exactly [`declare_sum_range_equations`]'s
//! own pattern one level deeper. `sumRange f (succ n)` already ι-reduces to
//! `add (sumRange f n) (f n)` ([`declare_sum_range_equations`]'s own
//! content); what makes the `seq`-level law free is that `CReal.add`'s
//! representative is *also* a bare `mk (fun n => …) _` application
//! ([`super::declare_addition`]), so `seq (add x y) k` ι-reduces (through
//! the `CReal.rec`/`CReal.mk` projection [`super::declare_projections`]
//! builds) straight to `seq x (shift k) + seq y (shift k)`, no case split on
//! `x`, `y`, `k`, or `n` required — all of them stay free variables through
//! the whole reduction, which is why the general (`∀ n`) law needs no
//! induction, only ι and β.
//!
//! **This recursion is not the same thing as a *closed form*, and the closed
//! form is where the real cost lives.** Unwinding [`declare_sum_range_seq_equations`]
//! `n` times gives, writing `shift^m` for `shift` iterated `m` times
//! (`shift^0 := id`):
//!
//! ```text
//! seq (sumRange f n) k  =  Σ_{i<n} seq (f i) (shift^{n−i} k)
//! ```
//!
//! i.e. `sumRange f n` sampled at `k` reads term `i` not at `i`'s own
//! canonical index, but at a *deep* index reached by iterating `shift` down
//! from `k`. This is a true statement — provable by induction on `n` from
//! the two equations above — but it is **not declared as a kernel theorem
//! here**, because stating it needs an explicit `Nat → Nat → Nat`
//! shift-iteration combinator (`shift` composed with itself a *symbolic*
//! number of times), which does not exist in this development and is its
//! own small piece of infrastructure (a `Nat.rec` definition plus its own
//! two defining equations, the same shape as [`declare_sum_range`] itself).
//!
//! Nor would the closed form, once stated, be *sufficient* to reach
//! `CReal.Cauchy (sumRange f)` for an arbitrary `f` — and seeing why is the
//! actual load-bearing finding of this slice. `Cauchy`'s bound has to be
//! **uniform in `n`** (one `K`, working for every pair of indices), but
//! bounding `seq (f i) (shift^{n−i} k)` against `f i`'s own canonical sample
//! `seq (f i) i` via [`super::CRealPrelude::regular`] costs
//! `modulus (shift^{n−i} k) i = 1/(shift^{n−i}(k)+1) + 1/(i+1)`. The first
//! term shrinks with more shifting; the **second does not shrink with
//! `n`** — it is `f i`'s own fixed regularity cost, unrelated to how deep
//! `sumRange` samples it. Summing that error over `i < n` costs at least
//! `Σ_{i<n} 1/(i+1)`, the harmonic series, which **diverges** as `n → ∞`. So
//! a per-term bound built this way cannot give a `Cauchy`-shaped estimate
//! uniform in `n`, for any `f` — the closed form is real, but it is the
//! wrong tool for this particular bridge, independent of how carefully it
//! is stated or proved.
//!
//! The tractable route is the one [`declare_sum_range_tail_le`] already
//! reaches partway: convert its **real-valued** tail bound (`CReal.le`,
//! already representative-independent) into a `Cauchy`-shaped raw bound by
//! widening at a *shared* index — the same three-term telescope
//! `completeness.rs::declare_limit_dist` runs (`seq (h m) m − seq (h n) n =
//! (seq (h m) m − seq (h m) j) + (seq (h m) j − seq (h n) j) + (seq (h n) j
//! − seq (h n) n)`, the outer two legs closed by [`super::CRealPrelude::regular`]
//! applied to the *fixed* reals `h m`/`h n` — no deep-shift indices involved
//! — and the middle leg by unfolding [`declare_sum_range_tail_le`]'s
//! `CReal.le` at that same shared index `j`, after deciding which of `m ≤ n`
//! or `n ≤ m` holds so the tail lemma has a `sum_range_split`-shaped
//! difference to work with). That still needs `CReal.abs`'s own `seq`
//! characterisation to unfold the middle leg (untouched by this slice), so
//! it is real remaining work, not a restatement — but it is bounded work of
//! the same shape `limit_dist` already solved, not a fresh harmonic-series
//! dead end.
//!
//! ## The Cauchy-shape conversion: the route closes, but it is a *nested*
//! telescope, not a flat one — read this before attempting it
//!
//! A later slice worked the construction above through to concrete term
//! level (never committed — see below for why) and the previous framing
//! understated its size by roughly 3–5×. The one paragraph above still
//! describes the *outer* structure correctly, but "the middle leg by
//! unfolding `sum_range_tail_le`'s `CReal.le`" is doing a lot of hidden
//! work: unfolding that `CReal.le` at the shared index gives a bound on
//! `seq (h m) j − seq (h n) j` **in terms of `seq (tail_g) j`**, i.e. in
//! terms of `g`'s own comparison-sequence sample at `j` — and `tail_g` is
//! itself `sumRange g (m+n) − sumRange g m`, an `add`/`neg` term whose
//! `seq` at `j` shifts (`seq (add x y) k` samples `x`, `y` at `shift k`,
//! never at `k`). Turning *that* into something usable needs a **second,
//! independent instance of the same three-leg telescope**, applied to `g`'s
//! own partial sums and anchored at `g`'s own Cauchy witness. Concretely,
//! for `CReal.sumRange_cauchy_of_dominated : ∀ f g, (∀ k, le (abs (f k)) (g
//! k)) → Cauchy (sumRange g) → Cauchy (sumRange f)` (the natural statement
//! of this piece — it has to conclude the *existential* `Cauchy`, not a bare
//! `Within`, because the bound it produces genuinely mentions `g`'s Cauchy
//! witness `K`, and only wrapping the conclusion in its own `∃ K'` lets that
//! dependency out of an `Exists.rec` motive):
//!
//! - **Outer telescope**, at shared index `t := shift q` (`q := m+n`, the
//!   ordering `sum_range_tail_le` already bakes in via its own `m`, `add m
//!   n` parameters — no `Nat.le_total` case split needed for *this* half):
//!   `seq (sumRange f m) m − seq (sumRange f q) q` splits into a leg from
//!   `CReal.regular (sumRange f m) m t`, a middle leg, and a leg from
//!   `CReal.regular (sumRange f q) t q`. The middle leg is (up to sign)
//!   `seq tail_f j` at `j := q`, bounded via `le_trans le_abs_self
//!   sum_range_tail_le` / `le_trans neg_le_abs sum_range_tail_le` (**two**
//!   one-sided real bounds, not one `abs_le` call, because `abs_le`'s
//!   hypothesis shape does not survive sampling at an index) applied at
//!   `q`, against `seq tail_g q`.
//! - **Inner telescope**, same shared-index shape but anchored through `m`
//!   and `q` themselves (not through `t` a second time): `seq tail_g q`
//!   unfolds (`add`'s own shift) to `seq (sumRange g q) t − seq (sumRange g
//!   m) t`, and *that* is bounded by routing through `seq (sumRange g m) m
//!   − seq (sumRange g q) q` — exactly `Cauchy (sumRange g)`'s witness
//!   applied at `(m, q)`, no index gymnastics needed for that piece — plus
//!   the same two `CReal.regular`-at-`(_, t)` legs used in the outer
//!   telescope (reused, not re-derived).
//!
//! **The sign/associativity bookkeeping is the actual cost, not the
//! mathematics.** Every `seq (add x y) k` unfold only gets you as far as
//! `Rat.sub`/`Rat.neg` applied in whatever nesting the source term had —
//! e.g. `seq (neg tail_f) q` reduces (pure ι/β, free) to `Rat.neg (Rat.sub
//! (seq A_q t) (seq A_m t))`, and turning that into the `Rat.sub (seq A_m
//! t) (seq A_q t)` shape the telescope's other legs use needs an *explicit*
//! `Rat.neg_sub` rewrite — defeq does computation, not ring identities, and
//! this construction needs the identity at nearly every join. `Rat.le_of_sub_le`
//! (`u ≤ v+q → ⊢ u−v ≤ q`, already declared) plus `Rat.neg_sub` supply the
//! sign flips; `Rat.sub_add_sub` supplies each telescoping join; `Rat.bounds_add`/
//! `Rat.bounds_neg` combine two-sided bounds; `half_shift_le`
//! (`completeness.rs`, already `pub(super)`) widens every `1/(shift q+1)`
//! leg up to `1/(q+1)` so `t` never survives into the final bound;
//! `Rat.nat_div_succ_add` fuses same-index terms and `Rat.nat_div_succ_le_add_left`
//! pads whichever of the two final coefficients is smaller so both sides
//! share one witness `K`, as `Cauchy`'s shape requires.
//!
//! Worked all the way through by hand, this is on the order of **35–45
//! distinct proof-term steps** (roughly matching `declare_converges_cauchy`
//! and `regroup_middle_four` combined, which solve a structurally similar
//! but *single*, not *nested*, three-term telescope) — **not committed this
//! slice**, because a construction this size, assembled in one pass without
//! kernel-checking each join, is exactly the failure mode this repository's
//! own history warns about (`EIGHT argument-position defects` in one day,
//! five in the `symm` family) and a kernel declaration has no "mostly
//! right" state: it either checks or it does not exist. The next attempt
//! should land the inner and outer telescopes as **separately kernel-tested
//! pieces** (e.g. first the `within`-swap-via-`neg_sub` helper and the
//! inner telescope alone, verified against a trivial `f = g` instance,
//! *then* the outer one) rather than as one unverified block.
//!
//! ## Two further gaps this slice found, neither in the previous brief
//!
//! Even a landed `sumRange_cauchy_of_dominated` does **not** reach `Σ b`
//! converges by itself, for a reason independent of the telescope above:
//!
//! 1. **There is no bridge from a `K`-scaled `Cauchy` witness to an actual
//!    limit.** `completeness.rs` builds `CReal.limit`/`CReal.limit_dist`
//!    only for `CReal.RegularSeq` — the **unscaled**, `K = 1` case
//!    (`modulus m n = 1/(m+1)+1/(n+1)` literally, not `≤`). Given `Cauchy f`
//!    with witness `K ≠ 1`, reindexing `f` to make it genuinely `K = 1`
//!    regular needs an *additional* regularity leg per sample (bounding
//!    `seq (f (σ n)) n` against `f (σ n)`'s own canonical sample `seq (f
//!    (σ n)) (σ n)`, for whatever reindexing `σ` is chosen) — a
//!    second, parametrised completeness construction, comparable in size to
//!    `completeness.rs` itself, that does not exist anywhere in this
//!    development yet. This blocks **both** `converges_geometric` (item 2)
//!    and the comparison test's conclusion (item 3, which needs an actual
//!    `Converges (sumRange a) L`, not just `Cauchy (sumRange a)`) — the
//!    comparison test does not avoid this by taking `Converges (sumRange
//!    b) M` as a hypothesis, because it still has to *produce* a limit for
//!    `sumRange a`.
//! 2. **`converges_geometric` needs a quantitative decay rate that also
//!    does not exist.** [`CRealPrelude::geom_tail_bounded`] bounds `(1 − x)
//!    · |tail| ≤ xᵐ`, not `|tail| ≤ xᵐ/(1 − x)` — going from the first to
//!    the second needs a "cancel a positive, apart-from-zero real factor
//!    from a `CReal.le`" lemma, and there is no such lemma over `CReal` in
//!    this codebase (checked: no `le_of_mul_le`/`div_le`/`le_div`/
//!    `mul_le_cancel` declared). And even granting that division, `Cauchy`'s
//!    shape needs `xᵐ ≤ C/(m+1)` for a *fixed* `C` — true for a witnessed
//!    ratio (`x ≤ N/(N+1)`) but itself a genuine calculus fact (Bernoulli's
//!    inequality or equivalent), not a restatement of anything already
//!    proved here.
//!
//! Net: the previous lane's "bounded work of the same shape `limit_dist`
//! already solved" undercounted by treating the tail-bound conversion as
//! the only remaining step. It is the first of at least three comparably
//! sized pieces (the nested telescope above; the `Cauchy`→`Converges`
//! reindexing bridge; the geometric decay-rate quantification), and none of
//! the three should be attempted as a single unverified slice.

use super::ring_helpers::add4_comm;
use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, creal_ty, div_succ, equiv, sample, shift, within,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, req, rle, rneg, rrefl, rzero};

/// Admit `CReal.sumRange`, its defining equations, congruence, additivity,
/// scalar distribution, monotonicity, and the triangle inequality.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_series(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_sum_range(d, p)?;
    declare_sum_range_equations(d, p)?;
    declare_sum_range_congr(d, p)?;
    declare_sum_range_add(d, p)?;
    declare_mul_sum_range(d, p)?;
    declare_sum_range_le(d, p)?;
    declare_abs_sum_range_le(d, p)?;
    declare_sum_range_telescope(d, p)?;
    declare_sum_range_split(d, p)?;
    declare_sum_range_tail_le(d, p)?;
    declare_sum_range_tail_within(d, p)?;
    declare_sum_range_seq_equations(d, p)
}

// --- small local term builders ----------------------------------------------

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

/// `λ k, f (add m k)` — `f` shifted by `m`, the summand
/// [`declare_sum_range_split`] and [`declare_sum_range_tail_le`] both build,
/// as one shared function so the two never drift into structurally distinct
/// (merely defeq) closures.
fn shifted_fn(d: &mut IntDev<'_>, m: ExprId, f: ExprId) -> ExprId {
    let nat_add = d.prelude().add;
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.const_app(nat_add, &[m, k]);
    let body = d.apply(f, &[mk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Eq.{1} CReal a b`.
fn creal_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let eq = d.kernel().const_(logic.eq, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} CReal a`.
fn creal_eq_refl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let refl = d.kernel().const_(logic.eq_refl, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(refl, &[carrier, a])
}

/// Chain `Equiv start …` through `(next, step)` pairs, the way
/// `super::product::equiv_chain`/`super::inverse::echain` do — rebuilt here
/// (both of those are private to their own modules) rather than imported.
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

/// `(a+b)+(c+d) ~ (a+c)+(b+d)`, returned as a `(target, proof)` chain step
/// (the proof's source is `add(add(a,b),add(c,d))`) — the `Equiv` promotion
/// of `nat_prelude/binomial.rs::add_add_add_comm`.
/// `Equiv (neg zero) zero`, as a proof term — the group identity `−0 = 0`,
/// from [`CRealPrelude::add_zero`]/[`CRealPrelude::add_comm`]/
/// [`CRealPrelude::add_neg`] rather than any `Rat`-level fact (`CReal` has no
/// standalone `neg_zero` law).
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]); // add nz zero ~ nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // nz ~ padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
    let h3 = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// `Equiv (neg (add a b)) (add (neg a) (neg b))` — additive inverse
/// distributes over `add`. Proved inline via [`add4_comm`] and the
/// additive-inverse laws by the usual "any right inverse of `a+b` is `−(a+b)`"
/// argument, specialised to the witness `(−a)+(−b)` rather than proved as a
/// general uniqueness lemma.
fn neg_add(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let s = cadd(d, p, a, b);
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let t = cadd(d, p, na, nb);
    let ns = cneg(d, p, s);

    // f_proof : Equiv (add s t) zero, via add4_comm + the two `add_neg`s.
    let f_proof = {
        let (target1, h4) = add4_comm(d, p, a, b, na, nb);
        // target1 = add (add a na) (add b nb)
        let a_na = cadd(d, p, a, na);
        let b_nb = cadd(d, p, b, nb);
        let add_zz = cadd(d, p, zero_c, zero_c);
        let h_a = d.lemma(p.add_neg, &[a]); // a_na ~ zero
        let h_b = d.lemma(p.add_neg, &[b]); // b_nb ~ zero
        let h5 = d.lemma(p.add_congr, &[a_na, zero_c, b_nb, zero_c, h_a, h_b]); // target1 ~ add_zz
        let h6 = d.lemma(p.add_zero, &[zero_c]); // add_zz ~ zero
        let start = cadd(d, p, s, t);
        echain(d, p, start, &[(target1, h4), (add_zz, h5), (zero_c, h6)])
    };

    // neg s ~ add(neg s)(zero) ~ add(neg s)(add s t) ~ (add(neg s)s)+t ~ add zero t ~ t
    let step_a_target = cadd(d, p, ns, zero_c);
    let step_a = {
        let h = d.lemma(p.add_zero, &[ns]); // step_a_target ~ ns
        d.lemma(p.equiv_symm, &[step_a_target, ns, h]) // ns ~ step_a_target
    };

    let st = cadd(d, p, s, t);
    let step_b_target = cadd(d, p, ns, st);
    let step_b = {
        let f_symm = d.lemma(p.equiv_symm, &[st, zero_c, f_proof]); // zero ~ add s t
        let refl_ns = d.lemma(p.equiv_refl, &[ns]);
        d.lemma(p.add_congr, &[ns, ns, zero_c, st, refl_ns, f_symm])
        // step_a_target ~ step_b_target
    };

    let ns_s = cadd(d, p, ns, s);
    let step_c_target = cadd(d, p, ns_s, t);
    let step_c = {
        let assoc = d.lemma(p.add_assoc, &[ns, s, t]); // step_c_target ~ step_b_target
        d.lemma(p.equiv_symm, &[step_c_target, step_b_target, assoc])
        // step_b_target ~ step_c_target
    };

    let step_d_target = cadd(d, p, zero_c, t);
    let step_d = {
        let x = {
            let comm = d.lemma(p.add_comm, &[ns, s]); // ns_s ~ add s ns
            let s_ns = cadd(d, p, s, ns);
            let negl = d.lemma(p.add_neg, &[s]); // add s ns ~ zero
            d.lemma(p.equiv_trans, &[ns_s, s_ns, zero_c, comm, negl])
        };
        // x : ns_s ~ zero
        let refl_t = d.lemma(p.equiv_refl, &[t]);
        d.lemma(p.add_congr, &[ns_s, zero_c, t, t, x, refl_t])
        // step_c_target ~ step_d_target
    };

    let t_zero = cadd(d, p, t, zero_c);
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

/// `Equiv (add (add a b) (neg a)) b` — the group cancellation `(a+b)+(−a) ~
/// b`, via `add_comm`, `add_assoc`, `add_neg`, `add_zero`.
fn cancel_right(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let ab = cadd(d, p, a, b);
    let start = cadd(d, p, ab, na);

    // (a+b)+(-a) ~ (b+a)+(-a)
    let ba = cadd(d, p, b, a);
    let comm1 = d.lemma(p.add_comm, &[a, b]); // ab ~ ba
    let refl_na = d.lemma(p.equiv_refl, &[na]);
    let s1 = cadd(d, p, ba, na);
    let h1 = d.lemma(p.add_congr, &[ab, ba, na, na, comm1, refl_na]);

    // (b+a)+(-a) ~ b+(a+(-a))
    let a_na = cadd(d, p, a, na);
    let s2 = cadd(d, p, b, a_na);
    let h2 = d.lemma(p.add_assoc, &[b, a, na]); // s1 ~ s2

    // b+(a+(-a)) ~ b+zero
    let zero_c = czero(d, p);
    let h_an = d.lemma(p.add_neg, &[a]); // a_na ~ zero
    let refl_b = d.lemma(p.equiv_refl, &[b]);
    let s3 = cadd(d, p, b, zero_c);
    let h3 = d.lemma(p.add_congr, &[b, b, a_na, zero_c, refl_b, h_an]); // s2 ~ s3

    // b+zero ~ b
    let h4 = d.lemma(p.add_zero, &[b]); // s3 ~ b

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (b, h4)])
}

/// `(target, proof)` with `target = add c b` and `proof : Equiv (add (add a
/// b) (add c (neg a))) target` — cancel `a` against its negation across a
/// four-term sum. Reorders the second pair via `add_comm` so
/// [`add4_comm`] lines `a` up against `neg a`, then one more `add_neg` /
/// `add_zero` / `add_comm` collapses the rest, mirroring [`neg_add`]'s own
/// "witness-specialised inverse" recipe.
fn cancel_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> (ExprId, ExprId) {
    let na = cneg(d, p, a);
    let ab = cadd(d, p, a, b);
    let c_na = cadd(d, p, c, na);
    let start = cadd(d, p, ab, c_na);

    // c+(-a) ~ (-a)+c
    let na_c = cadd(d, p, na, c);
    let comm1 = d.lemma(p.add_comm, &[c, na]); // c_na ~ na_c
    let refl_ab = d.lemma(p.equiv_refl, &[ab]);
    let s1 = cadd(d, p, ab, na_c);
    let h1 = d.lemma(p.add_congr, &[ab, ab, c_na, na_c, refl_ab, comm1]);

    // (a+b)+(na+c) ~ (a+na)+(b+c), via add4_comm(a,b,na,c)
    let (s2, h2) = add4_comm(d, p, a, b, na, c);

    // a+na ~ zero
    let a_na = cadd(d, p, a, na);
    let bc = cadd(d, p, b, c);
    let zero_c = czero(d, p);
    let h_an = d.lemma(p.add_neg, &[a]); // a_na ~ zero
    let refl_bc = d.lemma(p.equiv_refl, &[bc]);
    let s3 = cadd(d, p, zero_c, bc);
    let h3 = d.lemma(p.add_congr, &[a_na, zero_c, bc, bc, h_an, refl_bc]); // s2 ~ s3

    // zero+bc ~ bc+zero
    let bc_zero = cadd(d, p, bc, zero_c);
    let h4 = d.lemma(p.add_comm, &[zero_c, bc]); // s3 ~ bc_zero

    // bc+zero ~ bc
    let h5 = d.lemma(p.add_zero, &[bc]); // bc_zero ~ bc

    // bc ~ cb
    let cb = cadd(d, p, c, b);
    let h6 = d.lemma(p.add_comm, &[b, c]); // bc ~ cb
    let target = cb;

    let proof = echain(
        d,
        p,
        start,
        &[
            (s1, h1),
            (s2, h2),
            (s3, h3),
            (bc_zero, h4),
            (bc, h5),
            (target, h6),
        ],
    );
    (target, proof)
}

/// `le (abs (add a b)) (add (abs a) (abs b))` — the two-term triangle
/// inequality, from [`CRealPrelude::abs_le`] with
/// [`CRealPrelude::add_le_add`]/[`CRealPrelude::le_abs_self`] for the lower
/// branch and [`neg_add`] plus [`CRealPrelude::neg_le_abs`] for the upper
/// (negated) branch.
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
    let na_eq = neg_add(d, p, a, b); // ns ~ t
    let step1 = d.lemma(p.le_of_equiv, &[ns, t, na_eq]); // le ns t
    let nle_a = d.lemma(p.neg_le_abs, &[a]); // le na abs_a
    let nle_b = d.lemma(p.neg_le_abs, &[b]); // le nb abs_b
    let step2 = d.lemma(p.add_le_add, &[na, abs_a, nb, abs_b, nle_a, nle_b]); // le t bound
    let premise2 = d.lemma(p.le_trans, &[ns, t, bound, step1, step2]);

    d.lemma(p.abs_le, &[s, bound, premise1, premise2])
}

// --- the declarations --------------------------------------------------------

/// `CReal.sumRange : (Nat → CReal) → Nat → CReal`, structural `Nat.rec` on
/// the bound. See the module documentation for the convention.
fn declare_sum_range(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = d.kernel().const_(p.zero, vec![]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = d.const_app(p.add, &[ih, fj]);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, carrier);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 41),
    })
}

/// `CReal.sumRange_zero`/`CReal.sumRange_succ`: the defining equations of
/// [`declare_sum_range`], each closed by `Eq.refl` alone since `sumRange`'s
/// `Nat.rec` application ι-reduces on both minor premises.
fn declare_sum_range_equations(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    // sumRange_zero : ∀ f, Eq CReal (sumRange f Nat.zero) zero.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.sum_range, &[f, zero_n]);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        let stmt = creal_eq(d, p, lhs, zero_c);
        let proof = creal_eq_refl(d, p, zero_c);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // sumRange_succ : ∀ f (n : Nat),
    //   Eq CReal (sumRange f (succ n)) (add (sumRange f n) (f n)).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.sum_range, &[f, sn]);
        let prior = d.const_app(p.sum_range, &[f, n]);
        let fj = d.apply(f, &[n]);
        let rhs = d.const_app(p.add, &[prior, fj]);
        let stmt_inner = creal_eq(d, p, lhs, rhs);
        let proof_inner = creal_eq_refl(d, p, rhs);
        let ty = {
            let inner = d.pi_fv(n_fv, nat, stmt_inner);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(n_fv, nat, proof_inner);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.sumRange_congr : ∀ f g n, (∀ i, Equiv (f i) (g i)) → Equiv
/// (sumRange f n) (sumRange g n)`. Induction on `n`, mirroring
/// `Complex.sumRange_congr`'s own proof shape.
fn declare_sum_range_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let eqv = equiv(d, p, fi, gi);
        d.pi_fv(i_fv, nat, eqv)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = d.kernel().const_(p.zero, vec![]);
            d.lemma(p.equiv_refl, &[zero_c])
        },
        &|d, j, ih| {
            let f_prior = d.const_app(p.sum_range, &[f, j]);
            let g_prior = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);

            let start = d.const_app(p.add, &[f_prior, fj]);
            let mid = d.const_app(p.add, &[g_prior, fj]);
            let refl_fj = d.lemma(p.equiv_refl, &[fj]);
            let h1 = d.lemma(p.add_congr, &[f_prior, g_prior, fj, fj, ih, refl_fj]);

            let end = d.const_app(p.add, &[g_prior, gj]);
            let pointwise_j = d.apply(h, &[j]);
            let refl_g_prior = d.lemma(p.equiv_refl, &[g_prior]);
            let h2 = d.lemma(
                p.add_congr,
                &[g_prior, g_prior, fj, gj, refl_g_prior, pointwise_j],
            );

            d.lemma(p.equiv_trans, &[start, mid, end, h1, h2])
        },
        n,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, pointwise, stmt);
        let over_n = d.pi_fv(n_fv, nat, with_h);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise, proof);
        let over_n = d.lam_fv(n_fv, nat, with_h);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_add : ∀ f g n, Equiv (sumRange (fun i => add (f i) (g i))
/// n) (add (sumRange f n) (sumRange g n))`. Induction on `n`; the successor
/// case needs [`add4_comm`].
fn declare_sum_range_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let combined_fn = |d: &mut IntDev<'_>, f: ExprId, g: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = d.const_app(p.add, &[fi, gi]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let combined = combined_fn(d, f, g);
        let lhs = d.const_app(p.sum_range, &[combined, x]);
        let sf = d.const_app(p.sum_range, &[f, x]);
        let sg = d.const_app(p.sum_range, &[g, x]);
        let rhs = cadd(d, p, sf, sg);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let add_zz = cadd(d, p, zero_c, zero_c);
            let h = d.lemma(p.add_zero, &[zero_c]); // add zero zero ~ zero
            d.lemma(p.equiv_symm, &[add_zz, zero_c, h]) // zero ~ add zero zero
        },
        &|d, j, ih| {
            let combined = combined_fn(d, f, g);
            let scj = d.const_app(p.sum_range, &[combined, j]);
            let sf_j = d.const_app(p.sum_range, &[f, j]);
            let sg_j = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let fgj = cadd(d, p, fj, gj);

            let start = cadd(d, p, scj, fgj);
            let sfsg = cadd(d, p, sf_j, sg_j);
            let s1 = cadd(d, p, sfsg, fgj);
            let refl_fgj = d.lemma(p.equiv_refl, &[fgj]);
            let h1 = d.lemma(p.add_congr, &[scj, sfsg, fgj, fgj, ih, refl_fgj]);

            let (target, h2) = add4_comm(d, p, sf_j, sg_j, fj, gj);

            echain(d, p, start, &[(s1, h1), (target, h2)])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.mul_sumRange : ∀ w f n, Equiv (mul w (sumRange f n)) (sumRange
/// (fun i => mul w (f i)) n)` — a constant distributes through a finite sum,
/// mirroring `Complex.mul_sumRange`'s own proof shape.
fn declare_mul_sum_range(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = d.const_app(p.mul, &[w, fi]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs_sum = d.const_app(p.sum_range, &[f, x]);
        let lhs = d.const_app(p.mul, &[w, lhs_sum]);
        let scaled = scaled_fn(d);
        let rhs = d.const_app(p.sum_range, &[scaled, x]);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| d.lemma(p.mul_zero, &[w]),
        &|d, j, ih| {
            let prior = d.const_app(p.sum_range, &[f, j]);
            let fj = d.apply(f, &[j]);
            let extended = cadd(d, p, prior, fj);
            let start = d.const_app(p.mul, &[w, extended]);

            let w_prior = d.const_app(p.mul, &[w, prior]);
            let w_fj = d.const_app(p.mul, &[w, fj]);
            let distributed = cadd(d, p, w_prior, w_fj);
            let h1 = d.lemma(p.left_distrib, &[w, prior, fj]);

            let scaled = scaled_fn(d);
            let scaled_prior = d.const_app(p.sum_range, &[scaled, j]);
            let end = cadd(d, p, scaled_prior, w_fj);
            let refl_wfj = d.lemma(p.equiv_refl, &[w_fj]);
            let h2 = d.lemma(
                p.add_congr,
                &[w_prior, scaled_prior, w_fj, w_fj, ih, refl_wfj],
            );

            echain(d, p, start, &[(distributed, h1), (end, h2)])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        d.pi_fv(w_fv, carrier, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        d.lam_fv(w_fv, carrier, over_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_sum_range,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Nat.lt i n → le (f i) (g i)`, as a Pi type — the `Nat`-bounded pointwise
/// hypothesis [`declare_sum_range_le`] threads through induction, mirroring
/// `nat_prelude/binomial.rs::bounded_pointwise` with `CReal.le` in place of
/// `Eq Nat`.
fn bounded_le_pointwise(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    g: ExprId,
    bound: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let leq = cle(d, p, fi, gi);
    let body = d.arrow(hyp, leq);
    d.pi_fv(i_fv, nat, body)
}

/// `CReal.sumRange_le : ∀ f g n, (∀ i, Nat.lt i n → le (f i) (g i)) → le
/// (sumRange f n) (sumRange g n)` — monotonicity of a finite sum, with the
/// pointwise hypothesis restricted to indices below the bound, mirroring
/// `Nat.sumRange_congr_lt`'s hypothesis-threading shape
/// (`nat_prelude/binomial.rs::declare_sum_range_congr_lt`) promoted from `Eq`
/// to `CReal.le`.
fn declare_sum_range_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_le_pointwise(d, p, f, g, x);
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        let conclusion = cle(d, p, lhs, rhs);
        d.arrow(hyp, conclusion)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = bounded_le_pointwise(d, p, f, g, zero);
            let h_fv = d.fresh_fvar();
            let zero_c = czero(d, p);
            let body = d.lemma(p.le_refl, &[zero_c]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_le_pointwise(d, p, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // h_lt_j : ∀ i, Nat.lt i j → le (f i) (g i), weakened from `h`.
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let nat_p = d.prelude();
                let le_succ_j = d.lemma(nat_p.le_succ, &[j]);
                let lifted = d.lemma(nat_p.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let nat_p = d.prelude();
            let lt_j_sj = d.lemma(nat_p.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = d.const_app(p.sum_range, &[f, j]);
            let g_prior = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let body = d.lemma(p.add_le_add, &[f_prior, g_prior, fj, gj, sub1, sub2]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.abs_sumRange_le : ∀ f n, le (abs (sumRange f n)) (sumRange (fun k
/// => abs (f k)) n)` — the triangle inequality for finite sums, `|Σf| ≤
/// Σ|f|`. Induction on `n`, closing each step with [`abs_add_le`] chained
/// against the inductive hypothesis via [`CRealPrelude::add_le_add`] and
/// [`CRealPrelude::le_trans`].
fn declare_abs_sum_range_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let absf_fn = |d: &mut IntDev<'_>, f: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = cabs(d, p, fi);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sf = d.const_app(p.sum_range, &[f, x]);
        let lhs = cabs(d, p, sf);
        let absf = absf_fn(d, f);
        let rhs = d.const_app(p.sum_range, &[absf, x]);
        cle(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let le_refl_zero = d.lemma(p.le_refl, &[zero_c]);
            let nz_equiv = neg_zero_equiv(d, p);
            let nz = cneg(d, p, zero_c);
            let le_nz = d.lemma(p.le_of_equiv, &[nz, zero_c, nz_equiv]);
            d.lemma(p.abs_le, &[zero_c, zero_c, le_refl_zero, le_nz])
        },
        &|d, j, ih| {
            let sf_j = d.const_app(p.sum_range, &[f, j]);
            let fj = d.apply(f, &[j]);
            let absf = absf_fn(d, f);
            let saf_j = d.const_app(p.sum_range, &[absf, j]);
            let abs_fj = cabs(d, p, fj);
            let abs_sf_j = cabs(d, p, sf_j);

            let sf_plus_fj = cadd(d, p, sf_j, fj);
            let start = cabs(d, p, sf_plus_fj);
            let mid = cadd(d, p, abs_sf_j, abs_fj);
            let target = cadd(d, p, saf_j, abs_fj);

            let part1 = abs_add_le(d, p, sf_j, fj); // le(start, mid)
            let refl_abs_fj = d.lemma(p.le_refl, &[abs_fj]);
            let part2 = d.lemma(
                p.add_le_add,
                &[abs_sf_j, saf_j, abs_fj, abs_fj, ih, refl_abs_fj],
            ); // le(mid, target)

            d.lemma(p.le_trans, &[start, mid, target, part1, part2])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.abs_sum_range_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_telescope : ∀ f n, Equiv (sumRange (fun k => add (f (succ
/// k)) (neg (f k))) n) (add (f n) (neg (f Nat.zero)))` — `Σ_{k<n} (f(k+1) −
/// f k) ~ f n − f 0`. Induction on `n`: the base case is `symm add_neg`; the
/// successor case rewrites the inductive hypothesis into the accumulated sum
/// via `add_congr`, then closes with [`cancel_left`].
fn declare_sum_range_telescope(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let step_fn = |d: &mut IntDev<'_>, f: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let f_sk = d.apply(f, &[sk]);
        let f_k = d.apply(f, &[k]);
        let neg_fk = cneg(d, p, f_k);
        let body = cadd(d, p, f_sk, neg_fk);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };

    let zero_n = d.zero();
    let f0 = d.apply(f, &[zero_n]);
    let neg_f0 = cneg(d, p, f0);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let g = step_fn(d, f);
        let lhs = d.const_app(p.sum_range, &[g, x]);
        let fx = d.apply(f, &[x]);
        let rhs = cadd(d, p, fx, neg_f0);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let target = cadd(d, p, f0, neg_f0);
            let zero_c = czero(d, p);
            let h = d.lemma(p.add_neg, &[f0]); // Equiv target zero
            d.lemma(p.equiv_symm, &[target, zero_c, h])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange g j) (add (f j) (neg (f 0)))
            let fj = d.apply(f, &[j]);
            let neg_fj = cneg(d, p, fj);
            let sj = d.succ(j);
            let fsj = d.apply(f, &[sj]);
            let g = step_fn(d, f);
            let sum_gj = d.const_app(p.sum_range, &[g, j]);
            let gj = cadd(d, p, fsj, neg_fj); // = g j, up to beta

            let start = cadd(d, p, sum_gj, gj); // = sumRange g (succ j), up to iota

            let fj_negf0 = cadd(d, p, fj, neg_f0);
            let refl_gj = d.lemma(p.equiv_refl, &[gj]);
            let s1 = cadd(d, p, fj_negf0, gj);
            let h1 = d.lemma(p.add_congr, &[sum_gj, fj_negf0, gj, gj, ih, refl_gj]);

            // s1 = (fj + neg_f0) + (fsj + neg_fj) ~ fsj + neg_f0
            let (target, h2) = cancel_left(d, p, fj, neg_f0, fsj);

            echain(d, p, start, &[(s1, h1), (target, h2)])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_telescope,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_split : ∀ f m n, Equiv (sumRange f (add m n)) (add
/// (sumRange f m) (sumRange (fun k => f (add m k)) n))`. Induction on `n`;
/// both cases close purely by `Nat.add`'s own iota-reduction (`add m
/// Nat.zero ≡ m`, `add m (succ j) ≡ succ (add m j)`) plus one
/// `add_zero`/`add_assoc` respectively — no new rational estimate, and the
/// lemma every "tail of a partial sum" argument opens with.
fn declare_sum_range_split(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sum_f_m = d.const_app(p.sum_range, &[f, m]);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let m_plus_x = d.const_app(nat_add, &[m, x]);
        let lhs = d.const_app(p.sum_range, &[f, m_plus_x]);
        let h = shifted_fn(d, m, f);
        let sum_h_x = d.const_app(p.sum_range, &[h, x]);
        let rhs = cadd(d, p, sum_f_m, sum_h_x);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let padded = cadd(d, p, sum_f_m, zero_c);
            let h = d.lemma(p.add_zero, &[sum_f_m]); // Equiv padded sum_f_m
            d.lemma(p.equiv_symm, &[padded, sum_f_m, h])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange f (add m j)) (add sum_f_m (sumRange h j))
            let h = shifted_fn(d, m, f);
            let sum_h_j = d.const_app(p.sum_range, &[h, j]);
            let m_plus_j = d.const_app(nat_add, &[m, j]);
            let fmj = d.apply(f, &[m_plus_j]); // = f (add m j) = h j, up to beta

            let sum_f_mj = d.const_app(p.sum_range, &[f, m_plus_j]);
            let start = cadd(d, p, sum_f_mj, fmj); // = sumRange f (add m (succ j)), up to iota

            let rhs_prior = cadd(d, p, sum_f_m, sum_h_j);
            let refl_fmj = d.lemma(p.equiv_refl, &[fmj]);
            let s1 = cadd(d, p, rhs_prior, fmj);
            let h1 = d.lemma(p.add_congr, &[sum_f_mj, rhs_prior, fmj, fmj, ih, refl_fmj]);

            let sum_h_j_plus_fmj = cadd(d, p, sum_h_j, fmj);
            let target = cadd(d, p, sum_f_m, sum_h_j_plus_fmj);
            let h2 = d.lemma(p.add_assoc, &[sum_f_m, sum_h_j, fmj]);

            echain(d, p, start, &[(s1, h1), (target, h2)])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        d.pi_fv(f_fv, fn_ty, over_m)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        d.lam_fv(f_fv, fn_ty, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_split,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_tail_le : ∀ f g m n, (∀ k, le (abs (f k)) (g k)) → le (abs
/// (add (sumRange f (add m n)) (neg (sumRange f m)))) (add (sumRange g (add m
/// n)) (neg (sumRange g m)))` — **the comparison test**: an `m`-to-`m+n` tail
/// of `f`'s partial sums is bounded by the corresponding tail of `g`'s,
/// whenever `f` is pointwise bounded by `g` in absolute value.
///
/// Not stated through `CReal.Cauchy` — see the module documentation for why.
/// Both tails are rewritten to a shifted partial sum via [`declare_sum_range_split`]
/// and [`cancel_right`] (`(sumRange f m + sumRange h n) + (-(sumRange f m)) ~
/// sumRange h n`), then chained through [`CRealPrelude::abs_congr`],
/// [`CRealPrelude::abs_sum_range_le`] and [`CRealPrelude::sum_range_le`] (the
/// pointwise hypothesis applied at the shifted index) with three
/// [`CRealPrelude::le_trans`] steps.
fn declare_sum_range_tail_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pointwise_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let abs_fk = cabs(d, p, fk);
        let leq = cle(d, p, abs_fk, gk);
        d.pi_fv(k_fv, nat, leq)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let m_plus_n = d.const_app(nat_add, &[m, n]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, m_plus_n]);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail_f = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let sum_g_mn = d.const_app(p.sum_range, &[g, m_plus_n]);
    let sum_g_m = d.const_app(p.sum_range, &[g, m]);
    let neg_sum_g_m = cneg(d, p, sum_g_m);
    let tail_g = cadd(d, p, sum_g_mn, neg_sum_g_m);

    let abs_tail_f = cabs(d, p, tail_f);
    let target = cle(d, p, abs_tail_f, tail_g);

    let h_f = shifted_fn(d, m, f);
    let h_g = shifted_fn(d, m, g);
    let sum_hf_n = d.const_app(p.sum_range, &[h_f, n]);
    let sum_hg_n = d.const_app(p.sum_range, &[h_g, n]);

    // tail_f ~ sum_hf_n, via sumRange_split[f,m,n] + cancel_right.
    let split_f = d.lemma(p.sum_range_split, &[f, m, n]); // Equiv sum_f_mn (add sum_f_m sum_hf_n)
    let sum_f_m_plus_hf = cadd(d, p, sum_f_m, sum_hf_n);
    let refl_neg_f = d.lemma(p.equiv_refl, &[neg_sum_f_m]);
    let step_a = d.lemma(
        p.add_congr,
        &[
            sum_f_mn,
            sum_f_m_plus_hf,
            neg_sum_f_m,
            neg_sum_f_m,
            split_f,
            refl_neg_f,
        ],
    ); // Equiv tail_f (add sum_f_m_plus_hf neg_sum_f_m)
    let middle_f = cadd(d, p, sum_f_m_plus_hf, neg_sum_f_m);
    let cancel_f = cancel_right(d, p, sum_f_m, sum_hf_n); // Equiv middle_f sum_hf_n
    let tail_f_equiv = d.lemma(
        p.equiv_trans,
        &[tail_f, middle_f, sum_hf_n, step_a, cancel_f],
    );

    // tail_g ~ sum_hg_n, identically.
    let split_g = d.lemma(p.sum_range_split, &[g, m, n]);
    let sum_g_m_plus_hg = cadd(d, p, sum_g_m, sum_hg_n);
    let refl_neg_g = d.lemma(p.equiv_refl, &[neg_sum_g_m]);
    let step_b = d.lemma(
        p.add_congr,
        &[
            sum_g_mn,
            sum_g_m_plus_hg,
            neg_sum_g_m,
            neg_sum_g_m,
            split_g,
            refl_neg_g,
        ],
    );
    let middle_g = cadd(d, p, sum_g_m_plus_hg, neg_sum_g_m);
    let cancel_g = cancel_right(d, p, sum_g_m, sum_hg_n); // Equiv middle_g sum_hg_n
    let tail_g_equiv = d.lemma(
        p.equiv_trans,
        &[tail_g, middle_g, sum_hg_n, step_b, cancel_g],
    );

    // r1 : le abs_tail_f (abs sum_hf_n)
    let abs_sum_hf_n = cabs(d, p, sum_hf_n);
    let abs_congr_f = d.lemma(p.abs_congr, &[tail_f, sum_hf_n, tail_f_equiv]);
    let r1 = d.lemma(p.le_of_equiv, &[abs_tail_f, abs_sum_hf_n, abs_congr_f]);

    // r2 : le (abs sum_hf_n) (sumRange |h_f| n)
    let absf_hf = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hfi = d.apply(h_f, &[i]);
        let body = cabs(d, p, hfi);
        d.lam_fv(i_fv, nat, body)
    };
    let sum_absf_hf_n = d.const_app(p.sum_range, &[absf_hf, n]);
    let r2 = d.lemma(p.abs_sum_range_le, &[h_f, n]);

    // r3 : le (sumRange |h_f| n) sum_hg_n, via sumRange_le, pointwise from `hyp`.
    let pointwise_proof = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_fv = d.fresh_fvar();
        let lt_ty = d.lt(i, n);
        let mi = d.const_app(nat_add, &[m, i]);
        let applied = d.apply(hyp, &[mi]); // le (abs (f (add m i))) (g (add m i))
        let inner = d.lam_fv(lt_fv, lt_ty, applied);
        d.lam_fv(i_fv, nat, inner)
    };
    let r3 = d.lemma(p.sum_range_le, &[absf_hf, h_g, n, pointwise_proof]);

    // r4 : le sum_hg_n tail_g
    let tail_g_symm = d.lemma(p.equiv_symm, &[tail_g, sum_hg_n, tail_g_equiv]);
    let r4 = d.lemma(p.le_of_equiv, &[sum_hg_n, tail_g, tail_g_symm]);

    let c1 = d.lemma(
        p.le_trans,
        &[abs_tail_f, abs_sum_hf_n, sum_absf_hf_n, r1, r2],
    );
    let c2 = d.lemma(p.le_trans, &[abs_tail_f, sum_absf_hf_n, sum_hg_n, c1, r3]);
    let proof_body = d.lemma(p.le_trans, &[abs_tail_f, sum_hg_n, tail_g, c2, r4]);

    let ty = {
        let after_hyp = d.arrow(pointwise_ty, target);
        let over_n = d.pi_fv(n_fv, nat, after_hyp);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hyp = d.lam_fv(hyp_fv, pointwise_ty, proof_body);
        let over_n = d.lam_fv(n_fv, nat, with_hyp);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_tail_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// From `Rat.le (Rat.sub u v) w` and `Rat.le (Rat.sub (Rat.neg u) v) w`,
/// derive `CReal.Within u (Rat.add v w)` — the "within-swap via `neg_sub`"
/// helper the module documentation names as the first piece to land. It is
/// what turns the two one-sided `CReal.le`-unfolded bounds
/// (`le_trans le_abs_self sum_range_tail_le` /
/// `le_trans neg_le_abs sum_range_tail_le`, each applied at a shared index)
/// into the single `Within` bound the outer telescope's middle leg needs,
/// rather than one `abs_le` call — `abs_le`'s hypothesis shape does not
/// survive sampling at an index.
///
/// Modelled on [`super::weaken`]'s own `neg_le_neg` + rewrite pattern: the
/// upper half is `le_of_sub_le` outright; the lower half is `le_of_sub_le`
/// on `h2`, then `neg_le_neg` to flip it, then one `neg_neg` rewrite to
/// strip the resulting double negation back off `u` (`Rat`'s `neg_neg` is a
/// proved theorem, not a computation, so this rewrite is not optional the
/// way it would be over `CReal`'s ι-reducing `neg`).
fn within_of_tail_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    w: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let rat = p.rat;
    let vw = radd(d, v, w);

    // upper : le u vw
    let upper = d.lemma(rat.le_of_sub_le, &[u, v, w, h1]);

    // lower_neg : le (neg u) vw
    let neg_u = rneg(d, u);
    let lower_neg = d.lemma(rat.le_of_sub_le, &[neg_u, v, w, h2]);

    // flipped : le (neg vw) (neg (neg u))
    let neg_vw = rneg(d, vw);
    let neg_neg_u = rneg(d, neg_u);
    let flipped = d.lemma(rat.neg_le_neg, &[neg_u, vw, lower_neg]);

    // nn : Eq (neg (neg u)) u; lower : le (neg vw) u.
    let nn = d.lemma(rat.neg_neg, &[u]);
    let lower = rat_eq_rewrite(d, neg_neg_u, u, nn, flipped, &|d, t| rle(d, rat, neg_vw, t));

    let lower_ty = rle(d, rat, neg_vw, u);
    let upper_ty = rle(d, rat, u, vw);
    and_intro(d, p, lower_ty, upper_ty, lower, upper)
}

/// `CReal.sumRange_tail_within`. See the field documentation
/// ([`super::CRealPrelude::sum_range_tail_within`]) and this module's own
/// documentation for what this theorem is and is not: the middle leg the
/// outer telescope needs, not the telescope itself.
///
/// Reuses [`declare_sum_range_tail_le`]'s own `tail_f`/`tail_g`
/// construction verbatim, chains `le_abs_self`/`neg_le_abs` through
/// `le_trans` against that theorem's conclusion to get the two one-sided
/// `CReal.le` facts, applies each at the tail's own index `add m n`
/// (**not** at a further-shifted index — `CReal.add`'s own shift already
/// lands both `tail_f`'s and `tail_g`'s samples at `shift (add m n)`
/// automatically, by ι-reduction, once sampled at `add m n`), and closes
/// with [`within_of_tail_le`].
fn declare_sum_range_tail_within(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pointwise_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let abs_fk = cabs(d, p, fk);
        let leq = cle(d, p, abs_fk, gk);
        d.pi_fv(k_fv, nat, leq)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let m_plus_n = d.const_app(nat_add, &[m, n]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, m_plus_n]);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail_f = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let sum_g_mn = d.const_app(p.sum_range, &[g, m_plus_n]);
    let sum_g_m = d.const_app(p.sum_range, &[g, m]);
    let neg_sum_g_m = cneg(d, p, sum_g_m);
    let tail_g = cadd(d, p, sum_g_mn, neg_sum_g_m);

    // tail_le : CReal.le (abs tail_f) tail_g
    let tail_le = d.lemma(p.sum_range_tail_le, &[f, g, m, n, hyp]);
    let abs_tail_f = cabs(d, p, tail_f);

    // r1 : CReal.le tail_f tail_g
    let le_abs_self_f = d.lemma(p.le_abs_self, &[tail_f]);
    let r1 = d.lemma(
        p.le_trans,
        &[tail_f, abs_tail_f, tail_g, le_abs_self_f, tail_le],
    );

    // r2 : CReal.le (neg tail_f) tail_g
    let neg_tail_f = cneg(d, p, tail_f);
    let neg_le_abs_f = d.lemma(p.neg_le_abs, &[tail_f]);
    let r2 = d.lemma(
        p.le_trans,
        &[neg_tail_f, abs_tail_f, tail_g, neg_le_abs_f, tail_le],
    );

    // Both applied at the tail's own defining index.
    let r1_mn = d.apply(r1, &[m_plus_n]);
    let r2_mn = d.apply(r2, &[m_plus_n]);

    let u = sample(d, p, tail_f, m_plus_n);
    let v = sample(d, p, tail_g, m_plus_n);
    let w = div_succ(d, p, 2, m_plus_n);

    let value_body = within_of_tail_le(d, p, u, v, w, r1_mn, r2_mn);

    let ty = {
        let vw = radd(d, v, w);
        let claim = within(d, p, u, vw);
        let after_hyp = d.arrow(pointwise_ty, claim);
        let over_n = d.pi_fv(n_fv, nat, after_hyp);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hyp = d.lam_fv(hyp_fv, pointwise_ty, value_body);
        let over_n = d.lam_fv(n_fv, nat, with_hyp);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_tail_within,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_seq_zero`/`CReal.sumRange_seq_succ` — the recursive
/// sample-rate law. See the module documentation for the closed form it
/// implies, why that closed form is not declared here, and why it would not
/// by itself be enough to reach `CReal.Cauchy`.
///
/// Both close by `Eq.refl` alone: `sumRange f Nat.zero` ι-reduces to `zero :=
/// ofRat Rat.zero`, and `seq (ofRat q) k` ι-reduces to `q`
/// ([`super::declare_of_rat`]); `sumRange f (succ n)` ι-reduces to `add
/// (sumRange f n) (f n)`, and `seq (add x y) k` ι-reduces (through
/// `CReal.add`'s own `mk (fun n => …) _` representative,
/// [`super::declare_addition`]) to `seq x (shift k) + seq y (shift k)`.
fn declare_sum_range_seq_equations(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    // sumRange_seq_zero : ∀ f k, Eq Rat (seq (sumRange f Nat.zero) k) Rat.zero.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_n = d.zero();
        let sf = d.const_app(p.sum_range, &[f, zero_n]);
        let lhs = sample(d, p, sf, k);
        let rat_zero = rzero(d, p.rat);
        let stmt = req(d, lhs, rat_zero);
        let proof = rrefl(d, rat_zero);
        let value = {
            let inner = d.lam_fv(k_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        let ty = {
            let inner = d.pi_fv(k_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_seq_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // sumRange_seq_succ : ∀ f n k,
    //   Eq Rat (seq (sumRange f (succ n)) k)
    //          (add (seq (sumRange f n) (shift k)) (seq (f n) (shift k))).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let sn = d.succ(n);
        let sf_sn = d.const_app(p.sum_range, &[f, sn]);
        let lhs = sample(d, p, sf_sn, k);

        let sk = shift(d, k);
        let sf_n = d.const_app(p.sum_range, &[f, n]);
        let left_sample = sample(d, p, sf_n, sk);
        let fn_at_n = d.apply(f, &[n]);
        let right_sample = sample(d, p, fn_at_n, sk);
        let rhs = radd(d, left_sample, right_sample);

        let stmt = req(d, lhs, rhs);
        let proof = rrefl(d, rhs);

        let value = {
            let inner = d.lam_fv(k_fv, nat, proof);
            let over_n = d.lam_fv(n_fv, nat, inner);
            d.lam_fv(f_fv, fn_ty, over_n)
        };
        let ty = {
            let inner = d.pi_fv(k_fv, nat, stmt);
            let over_n = d.pi_fv(n_fv, nat, inner);
            d.pi_fv(f_fv, fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_seq_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}
