//! **`CReal.expTerm`/`CReal.expSeriesPartial`**: the rational term `1/n!`
//! embedded into `CReal`, and its `sumRange` partial sums — the raw material
//! for Euler's number `e := lim_k Σ_{n<k} 1/n!`.
//!
//! ## What this file builds, and what it does not (yet)
//!
//! [`declare_exp_term`] builds `CReal.expTerm n := ofRat (1/n!)`, using
//! `Nat.factorial` (`nat_prelude/defs.rs`, consumed here through `IntDev`'s
//! `NatOps` impl — no new `Nat`-level declaration needed) and
//! `Rat.normalize` (`int_prelude/rat.rs`) fed `Nat.one_le_factorial : ∀ n, 1
//! ≤ n!` (`nat_prelude/primes.rs`) as the denominator's positivity witness.
//! `Rat.normalize`'s own reducedness bookkeeping (`gcd`) is entirely internal
//! — this file never touches it.
//!
//! [`declare_exp_series_partial`] is the thin wrapper `CReal.expSeriesPartial
//! := CReal.sumRange CReal.expTerm`, so `expSeriesPartial k` unfolds by two
//! rounds of `Nat.rec` ι-reduction (`sumRange`'s own recursion, then
//! `CReal.add`'s constant-sequence arithmetic once every summand is `ofRat`
//! of a literal) to a concrete `CReal`, checked directly against `ofRat` of
//! the expected rational in `creal_tests.rs`.
//!
//! **This file does not yet establish `Cauchy (sumRange expTerm)`, and so
//! does not build `CReal.e`.** That needs a dominating `g : Nat → CReal`
//! with `Cauchy (sumRange g)` already in hand (`CReal.sumRange_
//! converges_of_dominated` takes exactly that plus the pointwise bound and
//! hands back `∃ L, Converges (sumRange f) L` in one call — see
//! `series.rs::declare_sum_range_converges_of_dominated`). The paper
//! domination is `1/n! ≤ 2·(1/2)ⁿ` for every `n` (no case split needed: both
//! sides are `2` at `n = 0`, both `1` at `n = 1`, and the ratio only widens
//! from there), which reduces to the `Nat` fact `n + 1 ≤ 2ⁿ` — a clean
//! induction, unconditional on `n`. What is genuinely missing is the bridge
//! from that pointwise fact to `Cauchy (sumRange g)` for a concrete `g`, and
//! nothing in `creal/power.rs` or `creal/archimedean_squeeze.rs` supplies it
//! for *any* geometric sequence yet (this is the first attempt to build one):
//! `power.rs`'s own module documentation is explicit that `geom_tail_bounded`
//! stops at `(1 − x)·tail ≤ xᵐ` — a `CReal`-valued bound, not a rational
//! schedule — specifically *because* going further needs `inv (1 − x)` with a
//! witnessed `PosBound`, which this module never has for `x := ofRat (1/2)`
//! (the CReal-level `inv` docs are the same restriction `sqrt.rs` names: `inv`
//! needs a *decided* apartness-from-zero it cannot manufacture from `0 ≤ x`
//! alone). Two routes exist and neither is built: (a) relate `CReal.pow
//! (ofRat (1/2)) n` to `ofRat ((1/2)^n)` via `of_rat_mul`/`pow_congr`
//! induction, then find an order lemma that multiplies an `CReal.le` through
//! by the positive rational `2` (not present in `field.rs`/`order_extra.rs`
//! as checked); or (b) skip `CReal.pow` and `Rat.normalize` a genuinely
//! rational geometric bound `g n := ofRat (2 / 2ⁿ)`, then prove `Cauchy
//! (sumRange g)` directly from the finite rational geometric-sum identity —
//! which itself does not exist at the `Rat` level either (`Nat.pow2_geom_sum`
//! is `Nat`-only). Either route is a new, self-contained lemma comparable in
//! size to `series.rs::declare_sum_range_cauchy_of_dominated` itself (the
//! *general* domination step this file's target would consume), not a
//! one-line application of what already exists.

use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, embed};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::normalize;

/// Height for `expTerm`/`expSeriesPartial`: both are thin definitional
/// wrappers (one `ofRat` application, one partial application of
/// `sumRange`), so one step above every `Rat`/`CReal` leaf they call is
/// enough — the callees' own heights govern how far *they* unfold.
const EXP_HEIGHT: u16 = DERIVED_HEIGHT + 1;

/// Admit `CReal.expTerm` and `CReal.expSeriesPartial`. See the module
/// documentation for what is deliberately not attempted here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exponential(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_exp_term(d, p)?;
    declare_exp_series_partial(d, p)
}

/// `Rat.normalize (Int.ofNat (Nat.succ Nat.zero)) (Nat.factorial n)
/// (Nat.one_le_factorial n)` — the rational `1/n!`, already reduced by
/// `Rat.normalize`'s own `gcd` bookkeeping.
fn inv_factorial(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);
    let denominator = d.factorial(n);
    let np = d.prelude();
    let positive = d.lemma(np.one_le_factorial, &[n]);
    normalize(d, one_int, denominator, positive)
}

/// `CReal.expTerm : Nat → CReal := fun n => ofRat (1/n!)`.
fn declare_exp_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let term = inv_factorial(d, n);
    let body = embed(d, p, term);

    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.exp_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXP_HEIGHT),
    })
}

/// `CReal.expSeriesPartial : Nat → CReal := CReal.sumRange CReal.expTerm`.
fn declare_exp_series_partial(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let exp_term = d.kernel().const_(p.exp_term, vec![]);
    let value = d.const_app(p.sum_range, &[exp_term]);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.exp_series_partial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXP_HEIGHT),
    })
}
