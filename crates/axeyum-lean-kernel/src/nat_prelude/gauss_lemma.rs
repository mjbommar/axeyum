//! Least-residue sign counting toward Gauss's lemma.
//!
//! `int_prelude/qr_criterion.rs`'s module doc names Gauss's lemma as one of
//! two routes to the second supplementary law of quadratic reciprocity (`2`
//! is a QR mod `p` iff `p ≡ ±1 (mod 8)`), and sizes it as "a
//! `Nat.countRange`-shaped least-residue sign-count ... this prelude does not
//! build". Re-measured (`shape_search --name-like countRange`, 19
//! declarations across `finite_set.rs`/`totient.rs`/`count_range_permute.rs`/
//! `count_range_reversal.rs`): the counting primitive and its subset/union/
//! compl/congr/split laws are real, usable machinery, not just names — this
//! file is the first consumer that builds a NEW `countRange` application
//! rather than reusing an existing totient-shaped one.
//!
//! ## What this file builds
//!
//! - [`declare_least_residue`]: `Nat.leastResidue pp a k := mod (mul a k)
//!   pp` — the least nonnegative residue of `a*k` mod `pp`, as a plain
//!   `Nat → Nat → Nat → Nat` function (no recursion of its own; it composes
//!   two already-declared primitives).
//! - [`declare_gauss_sign_neg`]: `Nat.gaussSignNeg pp a k : Bool := ble
//!   (succ (div pp 2)) (leastResidue pp a k)` — `true` exactly when the least
//!   residue exceeds `⌊pp/2⌋`, i.e. when the symmetric representative in
//!   `(-pp/2, pp/2]` is negative. This is the per-term sign Gauss's lemma
//!   counts.
//! - [`declare_gauss_neg_count`]: `Nat.gaussNegCount pp a m := countRange
//!   (fun j => gaussSignNeg pp a (succ j)) m` — folding the sign predicate
//!   over `k = 1, …, m` (the `succ j` shift moves `countRange`'s zero-based
//!   `[0, m)` index onto the classical one-based range).
//! - [`declare_gauss_residue_two_eq_double_of_lt`]: for the multiplier `a :=
//!   2` specifically, `mul 2 k < pp → leastResidue pp 2 k = mul 2 k` — since
//!   `k` never exceeds `m = (pp-1)/2`, `2*k` never reaches `pp` and the `mod`
//!   is a no-op (`Nat.mod_eq_self_of_lt`). This is what makes `a := 2` a
//!   genuinely easier case than the general lemma: the least-residue map is
//!   the identity-doubling map, not a real reduction.
//! - A table of concrete instances of `gaussNegCount` at `a := 2`, admitted
//!   axiom-free by the kernel's own `ι`-reduction (no proof term beyond
//!   `Eq.refl`, since every numeral involved stays under 25 — nowhere near
//!   this kernel's documented unary-numeral cost cliff), for `pp ∈ {7, 11,
//!   13, 17, 19, 23}` — one representative of each nonzero residue class mod
//!   8 among small odd primes (7 ≡ 7, 11 ≡ 3, 13 ≡ 5, 17 ≡ 1, 19 ≡ 3, 23 ≡
//!   7) — plus one instance at `a := 3` (`pp = 7`) to confirm the count
//!   genuinely depends on `a`, not only on `pp`. Every value was independently
//!   computed in Python before being written into a Rust theorem statement
//!   (see this module's `#[cfg(test)]` block for the script), per this
//!   repository's standing rule that a plan's "verified numerically" claim
//!   must be re-run, not inherited.
//!
//! ## What this does NOT reach
//!
//! Nothing here connects the sign count to `a^m mod pp` — that is the actual
//! content of Gauss's lemma (`a^m ≡ (-1)^gaussNegCount(pp,a,m) [pp]`), and it
//! needs the least-residue map's INJECTIVITY on `{1,…,m}`, a pairing lemma
//! (`r > pp/2 ⟹ pp - r` lands back among `{1,…,m}`'s residues), and a
//! product-cancellation argument (`Int.prodRange` exists in
//! `int_prelude/prod.rs`, built for Wilson's theorem, and is the right
//! carrier for it) — none of that is attempted here. This file only builds
//! the COUNTING half; the second supplementary law still needs the
//! connecting theorem plus a `p mod 8` case split on top of it. See
//! `docs/plan/status/gauss-lemma-countrange.md` for exact sizing.

use super::NatPrelude;
use super::group::{mod_eq_of_mod_eq_rel, mod_self_congr};
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Delta height for `Nat.leastResidue`: strictly above `Nat.mod`/`Nat.mul`
/// (both well under 10 in this prelude's numbering).
const LEAST_RESIDUE_HEIGHT: u16 = 32;
/// Strictly above [`LEAST_RESIDUE_HEIGHT`] (calls it) and `Nat.ble` (1).
const GAUSS_SIGN_NEG_HEIGHT: u16 = 33;
/// Strictly above [`GAUSS_SIGN_NEG_HEIGHT`] (calls it) and `Nat.countRange`
/// (12).
const GAUSS_NEG_COUNT_HEIGHT: u16 = 40;

/// `Nat.leastResidue(pp, a, k)`.
pub(super) fn least_residue(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.least_residue, &[pp, a, k])
}

/// `Nat.gaussSignNeg(pp, a, k)`.
pub(super) fn gauss_sign_neg(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.gauss_sign_neg, &[pp, a, k])
}

/// `Nat.gaussNegCount(pp, a, m)`.
pub(super) fn gauss_neg_count(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    m: ExprId,
) -> ExprId {
    d.const_app(p.gauss_neg_count, &[pp, a, m])
}

/// `Nat.leastResidue : Nat → Nat → Nat → Nat := fun pp a k => mod (mul a k) pp`.
///
/// Not recursive: it composes two already-declared primitives, so the
/// definition is a plain triple-lambda, no `Nat.rec` of its own.
pub(super) fn declare_least_residue(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pp_fv = d.fresh_fvar();
    let a_fv = d.fresh_fvar();
    let k_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a = d.kernel().fvar(a_fv);
    let k = d.kernel().fvar(k_fv);
    let ak = d.mul(a, k);
    let body = d.modulo(ak, pp);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_a = d.lam_fv(a_fv, nat, with_k);
        d.lam_fv(pp_fv, nat, with_a)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        let over_a = d.arrow(nat, over_k);
        d.arrow(nat, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.least_residue,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(LEAST_RESIDUE_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.gaussSignNeg : Nat → Nat → Nat → Bool :=
///   fun pp a k => ble (succ (div pp 2)) (leastResidue pp a k)`.
///
/// `true` exactly when the least residue of `a*k` mod `pp` exceeds `⌊pp/2⌋`
/// — i.e. when its symmetric representative in `(-pp/2, pp/2]` is negative.
pub(super) fn declare_gauss_sign_neg(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pp_fv = d.fresh_fvar();
    let a_fv = d.fresh_fvar();
    let k_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a = d.kernel().fvar(a_fv);
    let k = d.kernel().fvar(k_fv);
    let two = d.num(2);
    let half = d.div(pp, two);
    let succ_half = d.succ(half);
    let residue = least_residue(d, &p, pp, a, k);
    let body = d.ble(succ_half, residue);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_a = d.lam_fv(a_fv, nat, with_k);
        d.lam_fv(pp_fv, nat, with_a)
    };
    let ty = {
        let over_k = d.arrow(nat, bool_ty);
        let over_a = d.arrow(nat, over_k);
        d.arrow(nat, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.gauss_sign_neg,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(GAUSS_SIGN_NEG_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.gaussNegCount : Nat → Nat → Nat → Nat :=
///   fun pp a m => countRange (fun j => gaussSignNeg pp a (succ j)) m`.
///
/// The `succ j` shift moves `countRange`'s zero-based `[0, m)` fold onto the
/// classical one-based range `k = 1, …, m` Gauss's lemma counts over.
pub(super) fn declare_gauss_neg_count(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pp_fv = d.fresh_fvar();
    let a_fv = d.fresh_fvar();
    let m_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a = d.kernel().fvar(a_fv);
    let m = d.kernel().fvar(m_fv);
    let f = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let body = gauss_sign_neg(d, &p, pp, a, sj);
        d.lam_fv(j_fv, nat, body)
    };
    let body = d.const_app(p.count_range, &[f, m]);
    let value = {
        let with_m = d.lam_fv(m_fv, nat, body);
        let with_a = d.lam_fv(a_fv, nat, with_m);
        d.lam_fv(pp_fv, nat, with_a)
    };
    let ty = {
        let over_m = d.arrow(nat, nat);
        let over_a = d.arrow(nat, over_m);
        d.arrow(nat, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.gauss_neg_count,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(GAUSS_NEG_COUNT_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.gauss_residue_two_eq_double_of_lt : ∀ pp k,
///   Lt (mul 2 k) pp → Eq (leastResidue pp 2 k) (mul 2 k)`.
///
/// For the multiplier `a := 2`, whenever `2*k < pp` the least-residue map is
/// literally the doubling map — no reduction happens. Proof: unfold
/// `leastResidue pp 2 k` to `mod (mul 2 k) pp` (definitional) and apply
/// `Nat.mod_eq_self_of_lt`. Every caller with `k <= m` and `pp = 2*m+1`
/// satisfies the hypothesis, since `2*k <= 2*m = pp-1 < pp`.
pub(super) fn declare_gauss_residue_two_eq_double_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_residue_two_eq_double_of_lt, 2, &|d, v| {
        let (pp, k) = (v[0], v[1]);
        let two = d.num(2);
        let two_k = d.mul(two, k);
        let hyp_ty = d.lt(two_k, pp);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        // Eq (mod two_k pp) two_k -- and `least_residue(pp, two, k)` unfolds
        // (definitionally) to exactly `mod (mul two k) pp`, i.e. `mod two_k
        // pp`, so this proof checks against the stated conclusion below by
        // the kernel's own def_eq, no congruence step needed.
        let mod_eq = d.lemma(p.mod_eq_self_of_lt, &[two_k, pp, hyp]);
        let lhs = least_residue(d, &p, pp, two, k);
        let concl_ty = d.eq(lhs, two_k);
        let stmt = d.arrow(hyp_ty, concl_ty);
        let proof = d.lam_fv(hyp_fv, hyp_ty, mod_eq);
        (stmt, proof)
    })?;
    Ok(())
}

/// One concrete `gaussNegCount` instance, admitted axiom-free purely by the
/// kernel's own `ι`-reduction (`Eq.refl` at the final numeral) -- no proof
/// term beyond that reduction. `pp`/`a`/`m`/`expected` are all small enough
/// (`pp <= 23`) that this is nowhere near the unary-numeral cost cliff this
/// kernel's other declarations have hit at magnitudes in the thousands.
fn declare_gauss_neg_count_instance(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    name: crate::name::NameId,
    pp: u32,
    a: u32,
    m: u32,
    expected: u32,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(name, 0, &|d, _v| {
        let pp = d.num(pp);
        let a = d.num(a);
        let m = d.num(m);
        let lhs = gauss_neg_count(d, &p, pp, a, m);
        let rhs = d.num(expected);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        (stmt, proof)
    })?;
    Ok(())
}

/// `fun j => Nat.ble (Nat.succ half) (Nat.mul 2 (Nat.succ j))` -- the
/// generic sign predicate the closed-form induction counts, with `half`
/// captured as an outer parameter (not the induction variable).
fn closed_form_pred(d: &mut NatDev<'_>, half: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let two = d.num(2);
    let sj = d.succ(j);
    let two_sj = d.mul(two, sj);
    let succ_half = d.succ(half);
    let body = d.ble(succ_half, two_sj);
    d.lam_fv(j_fv, nat, body)
}

/// `Nat.mul 2 (Nat.succ x)`.
fn mul2succ(d: &mut NatDev<'_>, x: ExprId) -> ExprId {
    let two = d.num(2);
    let sx = d.succ(x);
    d.mul(two, sx)
}

/// `Nat.countRange(f, n)`.
fn count_range_of(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `h : Eq Bool a b |- Eq Nat (f a) (f b)` -- local copy of the `Bool`-
/// scrutinee, `Nat`-conclusion congruence `bitwise.rs`/`xor_algebra.rs` each
/// carry privately ([`NatOps::congr`]'s `eq_motive`/`transport` are
/// hardcoded to a `Nat`-typed hypothesis carrier, so it cannot express a
/// `Bool` hypothesis).
fn congr_bool_to_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `h : Eq Nat a b |- Eq Bool (f a) (f b)` -- local copy of
/// `subset_product.rs`'s private helper of the same shape ([`NatOps::congr`]
/// always closes into `Eq Nat`, so it cannot be reused for a `Bool`-valued
/// `f`).
fn congr_nat_to_bool(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.transport(a, motive, refl_case, b, h)
}

/// `h1 : Eq Bool a b`, `h2 : Eq Bool b c |- Eq Bool a c` -- the `Bool`-carrier
/// twin of [`NatOps::trans`] (hardcoded to a `Nat`-typed equality carrier).
fn bool_trans(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let motive = d.bool_eq_motive(b, &|d, x| d.bool_eq(a, x));
    d.bool_transport(b, motive, h1, c, h2)
}

/// `And.intro left_ty right_ty left right`.
fn and_intro2(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    d.const_app(p.logic.and_intro, &[left_ty, right_ty, left, right])
}

/// Two-way `Or` elimination: `ih : Or(left_ty, right_ty)`, and each branch
/// closure receives the branch's own hypothesis and must produce a proof of
/// `goal`. Mirrors `ops.rs`'s `cases_lt_bound`/`cases_lt_or_ge`, generalized
/// to an arbitrary (not necessarily `n`-indexed) `goal`.
#[allow(clippy::too_many_arguments)]
fn or_elim2(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    ih: ExprId,
    left_branch: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    right_branch: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let h_fv1 = d.fresh_fvar();
    let h1 = d.kernel().fvar(h_fv1);
    let lb_body = left_branch(d, h1);
    let lb = d.lam_fv(h_fv1, left_ty, lb_body);
    let h_fv2 = d.fresh_fvar();
    let h2 = d.kernel().fvar(h_fv2);
    let rb_body = right_branch(d, h2);
    let rb = d.lam_fv(h_fv2, right_ty, rb_body);
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let or_motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(or_rec, &[left_ty, right_ty, or_motive, lb, rb, ih])
}

/// Shared arithmetic scaffolding for the closed-form induction, computed
/// once per `half` and threaded through the base case and both step
/// branches: `t := div half 2`, and `lt_half_mul2_succt : Lt half
/// (mul 2 (succ t))` (ADR-0970's "established once, reused in A2 and B").
#[derive(Clone, Copy)]
struct ClosedFormCtx {
    half: ExprId,
    two: ExprId,
    one: ExprId,
    t: ExprId,
    mt: ExprId,
    mod_half_two: ExprId,
    sum_eq_half: ExprId,
    lt_half_mul2_succt: ExprId,
}

fn build_closed_form_ctx(d: &mut NatDev<'_>, p: &NatPrelude, half: ExprId) -> ClosedFormCtx {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let t = d.div(half, two);
    let mt = d.mul(two, t);
    let mod_half_two = d.modulo(half, two);

    let dme = d.lemma(p.div_mod_exec, &[one, half]);
    let sum = d.add(mt, mod_half_two);
    let dme_left_ty = d.eq(half, sum);
    let dme_right_ty = d.lt(mod_half_two, two);
    let dme_left = and_left(d, dme_left_ty, dme_right_ty, dme);
    let dme_right = and_right(d, dme_left_ty, dme_right_ty, dme);

    let mod_le_one = d.lemma(p.le_of_lt_succ, &[mod_half_two, one, dme_right]);
    let mt_add_one = d.add(mt, one);
    let sum_le = d.lemma(p.add_le_add_left, &[mt, mod_half_two, one, mod_le_one]);
    let sum_eq_half = d.symm(half, sum, dme_left);
    let half_le_mt_add_one = {
        let motive = d.eq_motive(sum, &|d, x| d.le(x, mt_add_one));
        d.transport(sum, motive, sum_le, half, sum_eq_half)
    };
    let lt_half_mul2_succt = d.lemma(p.lt_succ_of_le, &[half, mt_add_one, half_le_mt_add_one]);

    ClosedFormCtx {
        half,
        two,
        one,
        t,
        mt,
        mod_half_two,
        sum_eq_half,
        lt_half_mul2_succt,
    }
}

/// Base case (`x = 0`): left disjunct, `countRange f 0 = 0` by `refl` and
/// `0 <= t` by `zero_le`.
fn closed_form_base(d: &mut NatDev<'_>, p: &NatPrelude, ctx: ClosedFormCtx) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let f = closed_form_pred(d, ctx.half);
    let cf0 = count_range_of(d, &p, f, zero);
    let eq_ty = d.eq(cf0, zero);
    let le_ty = d.le(zero, ctx.t);
    let eq_proof = d.refl(zero);
    let le_proof = d.lemma(p.zero_le, &[ctx.t]);
    let left_ty = d.const_app(p.logic.and, &[eq_ty, le_ty]);
    let left_proof = and_intro2(d, &p, eq_ty, le_ty, eq_proof, le_proof);
    let right_le_ty = d.le(ctx.t, zero);
    let right_sum = d.add(cf0, ctx.t);
    let right_e_ty = d.eq(right_sum, zero);
    let right_ty = d.const_app(p.logic.and, &[right_le_ty, right_e_ty]);
    d.const_app(p.logic.or_inl, &[left_ty, right_ty, left_proof])
}

/// Step branch A1: `ih_a : Eq cj 0 /\ Le j t` and `hlt : Lt j t`. Shows
/// `f j = false` (the least residue of `2*(j+1)` stays below `half+1`), so
/// `countRange f (succ j) = countRange f j = 0` and the LEFT disjunct
/// survives to `succ j`.
fn closed_form_step_a1(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    ctx: ClosedFormCtx,
    j: ExprId,
    cj: ExprId,
    cj_eq0: ExprId,
    hlt: ExprId,
) -> ExprId {
    let p = *p;
    let sj = d.succ(j);
    let f = closed_form_pred(d, ctx.half);
    let fj = d.apply(f, &[j]);
    let m2sj = mul2succ(d, j);

    let mul_le = d.lemma(p.mul_le_mul_left, &[ctx.two, sj, ctx.t, hlt]);
    let le_add = d.lemma(p.le_add_right, &[ctx.mt, ctx.mod_half_two]);
    let sum = d.add(ctx.mt, ctx.mod_half_two);
    let le_mt_half = {
        let mt = ctx.mt;
        let motive = d.eq_motive(sum, &|d, x| d.le(mt, x));
        d.transport(sum, motive, le_add, ctx.half, ctx.sum_eq_half)
    };
    let chain1 = d.lemma(p.le_trans, &[m2sj, ctx.mt, ctx.half, mul_le, le_mt_half]);
    let lt_succ = d.lemma(p.lt_succ_of_le, &[m2sj, ctx.half, chain1]);
    let succ_half = d.succ(ctx.half);
    let fj_false = d.lemma(p.ble_eq_false_of_lt, &[succ_half, m2sj, lt_succ]);

    let zero = d.zero();
    let one = ctx.one;
    let bfalse = d.bool_false();
    let sel_eq0 = congr_bool_to_nat(d, fj, bfalse, fj_false, &|d, x| {
        let one = d.num(1);
        let zero = d.zero();
        d.bool_select_nat(x, one, zero)
    });
    let sel = d.bool_select_nat(fj, one, zero);
    let start = d.add(cj, sel);
    let step1 = d.congr(cj, zero, cj_eq0, &|d, x| d.add(x, sel));
    let mid1 = d.add(zero, sel);
    let step2 = d.congr(sel, zero, sel_eq0, &|d, x| d.add(zero, x));
    let mid2 = d.add(zero, zero);
    let (_end, csj_eq0) = d.chain(start, &[(mid1, step1), (mid2, step2)]);

    let csj = count_range_of(d, &p, f, sj);
    let e_ty = d.eq(csj, zero);
    let le_ty = d.le(sj, ctx.t);
    let left_ty = d.const_app(p.logic.and, &[e_ty, le_ty]);
    let left_proof = and_intro2(d, &p, e_ty, le_ty, csj_eq0, hlt);

    let right_le_ty = d.le(ctx.t, sj);
    let right_sum = d.add(csj, ctx.t);
    let right_e_ty = d.eq(right_sum, sj);
    let right_ty = d.const_app(p.logic.and, &[right_le_ty, right_e_ty]);

    d.const_app(p.logic.or_inl, &[left_ty, right_ty, left_proof])
}

/// Step branch A2: `ih_a : Eq cj 0 /\ Le j t` and `heq : Eq j t`. Shows
/// `f j = true`, so `countRange f (succ j) = 1` and the RIGHT disjunct opens
/// at `succ j` (`1 + t = succ j`, since `j = t`).
fn closed_form_step_a2(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    ctx: ClosedFormCtx,
    j: ExprId,
    cj: ExprId,
    cj_eq0: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let sj = d.succ(j);
    let f = closed_form_pred(d, ctx.half);
    let fj = d.apply(f, &[j]);

    let st = d.succ(ctx.t);
    let sj_eq_st = d.congr(j, ctx.t, heq, &|d, x| d.succ(x));
    let m2st = mul2succ(d, ctx.t);
    let m2sj = mul2succ(d, j);
    let m2sj_eq_m2st = d.congr(j, ctx.t, heq, &|d, x| mul2succ(d, x));
    let symm_m2 = d.symm(m2sj, m2st, m2sj_eq_m2st);
    let lt_half_m2sj = {
        let half = ctx.half;
        let motive = d.eq_motive(m2st, &|d, x| d.lt(half, x));
        d.transport(m2st, motive, ctx.lt_half_mul2_succt, m2sj, symm_m2)
    };
    let succ_half = d.succ(ctx.half);
    let fj_true = d.lemma(p.ble_eq_true_of_le, &[succ_half, m2sj, lt_half_m2sj]);

    let zero = d.zero();
    let one = ctx.one;
    let btrue = d.bool_true();
    let sel_eq1 = congr_bool_to_nat(d, fj, btrue, fj_true, &|d, x| {
        let one = d.num(1);
        let zero = d.zero();
        d.bool_select_nat(x, one, zero)
    });
    let sel = d.bool_select_nat(fj, one, zero);
    let start = d.add(cj, sel);
    let step1 = d.congr(cj, zero, cj_eq0, &|d, x| d.add(x, sel));
    let mid1 = d.add(zero, sel);
    let step2 = d.congr(sel, one, sel_eq1, &|d, x| d.add(zero, x));
    let mid2 = d.add(zero, one);
    let (_end, csj_eq1) = d.chain(start, &[(mid1, step1), (mid2, step2)]);

    let csj = count_range_of(d, &p, f, sj);

    let le_succ_t = d.lemma(p.le_succ, &[ctx.t]);
    let heq_symm = d.symm(j, ctx.t, heq);
    let t_le_sj = {
        let t = ctx.t;
        let motive = d.eq_motive(t, &|d, x| {
            let sx = d.succ(x);
            d.le(t, sx)
        });
        d.transport(t, motive, le_succ_t, j, heq_symm)
    };

    let add_comm_1t = d.lemma(p.add_comm, &[one, ctx.t]);
    let add1t = d.add(one, ctx.t);
    let addt1 = d.add(ctx.t, one);
    let symm_sj_eq_st = d.symm(sj, st, sj_eq_st);
    let (_end2, add1t_eq_sj) = d.chain(add1t, &[(addt1, add_comm_1t), (sj, symm_sj_eq_st)]);

    let final_start = d.add(csj, ctx.t);
    let step_a = d.congr(csj, one, csj_eq1, &|d, x| d.add(x, ctx.t));
    let mid_f = d.add(one, ctx.t);
    let (_end3, final_eq) = d.chain(final_start, &[(mid_f, step_a), (sj, add1t_eq_sj)]);

    let right_le_ty = d.le(ctx.t, sj);
    let right_sum = d.add(csj, ctx.t);
    let right_e_ty = d.eq(right_sum, sj);
    let right_proof = and_intro2(d, &p, right_le_ty, right_e_ty, t_le_sj, final_eq);
    let right_ty = d.const_app(p.logic.and, &[right_le_ty, right_e_ty]);

    let left_e_ty = d.eq(csj, zero);
    let left_le_ty = d.le(sj, ctx.t);
    let left_ty = d.const_app(p.logic.and, &[left_e_ty, left_le_ty]);

    d.const_app(p.logic.or_inr, &[left_ty, right_ty, right_proof])
}

/// Step branch B: `ih_b : Le t j /\ Eq (add cj t) j`. Shows `f j = true`
/// directly from `Le t j` (no need for `Eq j t`), so the RIGHT disjunct
/// survives to `succ j` unconditionally.
fn closed_form_step_b(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    ctx: ClosedFormCtx,
    j: ExprId,
    cj: ExprId,
    ih_b: ExprId,
) -> ExprId {
    let p = *p;
    let sj = d.succ(j);
    let f = closed_form_pred(d, ctx.half);
    let fj = d.apply(f, &[j]);

    let le_ty = d.le(ctx.t, j);
    let sum_j = d.add(cj, ctx.t);
    let e_ty = d.eq(sum_j, j);
    let t_le_j = and_left(d, le_ty, e_ty, ih_b);
    let cj_add_t_eq_j = and_right(d, le_ty, e_ty, ih_b);

    let succ_le = d.lemma(p.le_succ_succ, &[ctx.t, j, t_le_j]);
    let st = d.succ(ctx.t);
    let m2st = mul2succ(d, ctx.t);
    let m2sj = mul2succ(d, j);
    let mul_le = d.lemma(p.mul_le_mul_left, &[ctx.two, st, sj, succ_le]);
    let lt_half_m2sj = d.lemma(
        p.lt_of_lt_of_le,
        &[ctx.half, m2st, m2sj, ctx.lt_half_mul2_succt, mul_le],
    );
    let succ_half = d.succ(ctx.half);
    let fj_true = d.lemma(p.ble_eq_true_of_le, &[succ_half, m2sj, lt_half_m2sj]);

    let zero = d.zero();
    let one = ctx.one;
    let btrue = d.bool_true();
    let sel_eq1 = congr_bool_to_nat(d, fj, btrue, fj_true, &|d, x| {
        let one = d.num(1);
        let zero = d.zero();
        d.bool_select_nat(x, one, zero)
    });
    let sel = d.bool_select_nat(fj, one, zero);
    let cf_succ_eq = d.congr(sel, one, sel_eq1, &|d, x| d.add(cj, x));

    let le_succ_j = d.lemma(p.le_succ, &[j]);
    let t_le_sj = d.lemma(p.le_trans, &[ctx.t, j, sj, t_le_j, le_succ_j]);

    let s1_start = d.add(cj, sel);
    let s1_mid1 = d.add(cj, one);
    let start = d.add(s1_start, ctx.t);
    let mid1 = d.add(s1_mid1, ctx.t);
    let step_a = d.congr(s1_start, s1_mid1, cf_succ_eq, &|d, x| d.add(x, ctx.t));
    let s2 = d.add(cj, ctx.t);
    let mid2 = d.add(s2, one);
    let step_b = d.lemma(p.add_right_comm, &[cj, one, ctx.t]);
    let mid3 = d.add(j, one);
    let step_c = d.congr(s2, j, cj_add_t_eq_j, &|d, x| d.add(x, one));
    let (_end, final_eq) = d.chain(start, &[(mid1, step_a), (mid2, step_b), (mid3, step_c)]);

    let csj = count_range_of(d, &p, f, sj);

    let right_le_ty = d.le(ctx.t, sj);
    let right_sum = d.add(csj, ctx.t);
    let right_e_ty = d.eq(right_sum, sj);
    let right_proof = and_intro2(d, &p, right_le_ty, right_e_ty, t_le_sj, final_eq);
    let right_ty = d.const_app(p.logic.and, &[right_le_ty, right_e_ty]);

    let left_e_ty = d.eq(csj, zero);
    let left_le_ty = d.le(sj, ctx.t);
    let left_ty = d.const_app(p.logic.and, &[left_e_ty, left_le_ty]);

    d.const_app(p.logic.or_inr, &[left_ty, right_ty, right_proof])
}

/// The general closed-form counting invariant, by induction on `n` with
/// `half` (and `t := div half 2`) held fixed. See the `NatPrelude` field
/// doc for the exact statement (ADR-0970/ADR-0985).
pub(super) fn declare_gauss_count_ble_closed_form_disj(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_count_ble_closed_form_disj, 2, &|d, v| {
        let (half, n) = (v[0], v[1]);
        let ctx = build_closed_form_ctx(d, &p, half);
        let f = closed_form_pred(d, ctx.half);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let cx = count_range_of(d, &p, f, x);
            let zero = d.zero();
            let e = d.eq(cx, zero);
            let le = d.le(x, ctx.t);
            let left = d.const_app(p.logic.and, &[e, le]);
            let le2 = d.le(ctx.t, x);
            let sum = d.add(cx, ctx.t);
            let e2 = d.eq(sum, x);
            let right = d.const_app(p.logic.and, &[le2, e2]);
            d.const_app(p.logic.or, &[left, right])
        };
        let stmt = motive(d, n);

        let proof = d.induct(
            &motive,
            &|d| closed_form_base(d, &p, ctx),
            &|d, j, ih| {
                let sj = d.succ(j);
                let cj = count_range_of(d, &p, f, j);
                let csj = count_range_of(d, &p, f, sj);
                let zero = d.zero();

                let ih_left_eq_ty = d.eq(cj, zero);
                let ih_left_le_ty = d.le(j, ctx.t);
                let ih_left_ty = d.const_app(p.logic.and, &[ih_left_eq_ty, ih_left_le_ty]);
                let ih_right_le_ty = d.le(ctx.t, j);
                let ih_right_sum = d.add(cj, ctx.t);
                let ih_right_eq_ty = d.eq(ih_right_sum, j);
                let ih_right_ty = d.const_app(p.logic.and, &[ih_right_le_ty, ih_right_eq_ty]);

                let goal_left_eq_ty = d.eq(csj, zero);
                let goal_left_le_ty = d.le(sj, ctx.t);
                let goal_left_ty = d.const_app(p.logic.and, &[goal_left_eq_ty, goal_left_le_ty]);
                let goal_right_le_ty = d.le(ctx.t, sj);
                let goal_right_sum = d.add(csj, ctx.t);
                let goal_right_eq_ty = d.eq(goal_right_sum, sj);
                let goal_right_ty = d.const_app(p.logic.and, &[goal_right_le_ty, goal_right_eq_ty]);
                let goal = d.const_app(p.logic.or, &[goal_left_ty, goal_right_ty]);

                or_elim2(
                    d,
                    &p,
                    ih_left_ty,
                    ih_right_ty,
                    goal,
                    ih,
                    &|d, ih_a| {
                        let cj_eq_ty = d.eq(cj, zero);
                        let j_le_t_ty = d.le(j, ctx.t);
                        let cj_eq0 = and_left(d, cj_eq_ty, j_le_t_ty, ih_a);
                        let j_le_t = and_right(d, cj_eq_ty, j_le_t_ty, ih_a);
                        let disj = d.lemma(p.lt_or_eq_of_le, &[j, ctx.t, j_le_t]);
                        let lt_ty = d.lt(j, ctx.t);
                        let eq_ty = d.eq(j, ctx.t);
                        or_elim2(
                            d,
                            &p,
                            lt_ty,
                            eq_ty,
                            goal,
                            disj,
                            &|d, hlt| closed_form_step_a1(d, &p, ctx, j, cj, cj_eq0, hlt),
                            &|d, heq| closed_form_step_a2(d, &p, ctx, j, cj, cj_eq0, heq),
                        )
                    },
                    &|d, ih_b| closed_form_step_b(d, &p, ctx, j, cj, ih_b),
                )
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// From `disj : Disj(x, x, t)` (i.e. `Or(And(Eq cf 0, Le x t), And(Le t x,
/// Eq (add cf t) x))` for a fixed `cf`), derive `Eq cf (sub x t)`. Below `t`
/// the count is `0` and `sub x t` truncates to `0`
/// (`sub_eq_zero_of_le`); at or above `t`, `cf = sub x t` follows from
/// `add cf t = x` via `add_comm` + `add_sub_cancel_left`.
fn disj_to_sub_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cf: ExprId,
    x: ExprId,
    t: ExprId,
    disj: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let eq_ty = d.eq(cf, zero);
    let le_ty = d.le(x, t);
    let left_ty = d.const_app(p.logic.and, &[eq_ty, le_ty]);
    let le_ty2 = d.le(t, x);
    let sum = d.add(cf, t);
    let e_ty2 = d.eq(sum, x);
    let right_ty = d.const_app(p.logic.and, &[le_ty2, e_ty2]);

    let sub_xt = d.sub(x, t);
    let goal = d.eq(cf, sub_xt);

    or_elim2(
        d,
        &p,
        left_ty,
        right_ty,
        goal,
        disj,
        &|d, ih_a| {
            let cf_eq0 = and_left(d, eq_ty, le_ty, ih_a);
            let x_le_t = and_right(d, eq_ty, le_ty, ih_a);
            let sub_eq0 = d.lemma(p.sub_eq_zero_of_le, &[x, t, x_le_t]);
            let symm_sub = d.symm(sub_xt, zero, sub_eq0);
            d.trans(cf, zero, sub_xt, cf_eq0, symm_sub)
        },
        &|d, ih_b| {
            let cf_add_t_eq_x = and_right(d, le_ty2, e_ty2, ih_b);
            let symm_x = d.symm(sum, x, cf_add_t_eq_x);
            let sub_congr = d.congr(x, sum, symm_x, &|d, v| d.sub(v, t));

            let add_comm_cft = d.lemma(p.add_comm, &[cf, t]);
            let addtc = d.add(t, cf);
            let sub_comm_congr = d.congr(sum, addtc, add_comm_cft, &|d, v| d.sub(v, t));
            let cancel = d.lemma(p.add_sub_cancel_left, &[t, cf]);
            let sub_sum_t = d.sub(sum, t);
            let sub_addtc_t = d.sub(addtc, t);
            let (_end, unfold_eq) =
                d.chain(sub_sum_t, &[(sub_addtc_t, sub_comm_congr), (cf, cancel)]);

            let final_eq_rev = d.trans(sub_xt, sub_sum_t, cf, sub_congr, unfold_eq);
            d.symm(sub_xt, cf, final_eq_rev)
        },
    )
}

/// The symbolic closed form for `gaussNegCount` at `a := 2` and
/// `pp := 2*m+1` (the classical odd-prime shape): `gaussNegCount
/// (succ (mul 2 m)) 2 m = sub m (div m 2)`. Establishes `div pp 2 = m` via
/// `div_mod_unique`, bridges `gaussNegCount pp 2 m` to the general closed
/// form's `countRange` (`gauss_residue_two_eq_double_of_lt` +
/// `countRange_congr_lt`), then reads the value off the general closed-form
/// disjunction specialized at `half := m, n := m` (ADR-0970/ADR-0985).
pub(super) fn declare_gauss_neg_count_two_closed_form(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_neg_count_two_closed_form, 1, &|d, v| {
        let m = v[0];
        let two = d.num(2);
        let one = d.num(1);
        let mul_two_m = d.mul(two, m);
        let pp = d.succ(mul_two_m);

        // `divMod 2 pp m 1` via a direct witness: `pp` is literally
        // `add (mul two m) 1` up to defeq, and `Lt 1 2 = Le 2 2` (`le_refl`).
        let sum_pp = d.add(mul_two_m, one);
        let eq_ty = d.eq(pp, sum_pp);
        let lt_ty = d.lt(one, two);
        let eq_proof = d.refl(pp);
        let le22 = d.lemma(p.le_refl, &[two]);
        let witness = and_intro2(d, &p, eq_ty, lt_ty, eq_proof, le22);

        let dme = d.lemma(p.div_mod_exec, &[one, pp]);
        let dpp = d.div(pp, two);
        let mpp = d.modulo(pp, two);
        let unique = d.lemma(p.div_mod_unique, &[two, pp, dpp, mpp, m, one, dme, witness]);
        let q_eq_ty = d.eq(dpp, m);
        let r_eq_ty = d.eq(mpp, one);
        let dpp_eq_m = and_left(d, q_eq_ty, r_eq_ty, unique);

        let f = {
            let nat = d.nat_ty();
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let body = gauss_sign_neg(d, &p, pp, two, sj);
            d.lam_fv(j_fv, nat, body)
        };
        let g = closed_form_pred(d, m);

        // `pp = succ (mul two m)` gives `Lt (mul two m) pp` directly.
        let lt_mul2m_pp = d.lemma(p.le_refl, &[pp]);

        let nat = d.nat_ty();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_im = d.lt(i, m);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let eq_bool_ty = d.bool_eq(fi, gi);
        let hyp_body_ty = d.arrow(lt_im, eq_bool_ty);
        let hyp_pred = d.pi_fv(i_fv, nat, hyp_body_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let si = d.succ(i);
        let m2si = mul2succ(d, i);
        let m2m = d.mul(two, m);
        let mul_le = d.lemma(p.mul_le_mul_left, &[two, si, m, h]);
        let lt_m2si_pp = d.lemma(p.lt_of_le_of_lt, &[m2si, m2m, pp, mul_le, lt_mul2m_pp]);
        let residue_eq = d.lemma(p.gauss_residue_two_eq_double_of_lt, &[pp, si, lt_m2si_pp]);

        let mod_val = d.modulo(m2si, pp);
        let succ_m = d.succ(m);
        let succ_dpp = d.succ(dpp);
        let step1 = congr_nat_to_bool(d, dpp, m, dpp_eq_m, &|d, x| {
            let sx = d.succ(x);
            d.ble(sx, mod_val)
        });
        let ble_succdpp_modval = d.ble(succ_dpp, mod_val);
        let ble_succm_modval = d.ble(succ_m, mod_val);
        let step2 = congr_nat_to_bool(d, mod_val, m2si, residue_eq, &|d, x| d.ble(succ_m, x));
        let ble_succm_m2si = d.ble(succ_m, m2si);
        let chained = bool_trans(
            d,
            ble_succdpp_modval,
            ble_succm_modval,
            ble_succm_m2si,
            step1,
            step2,
        );

        let hyp_body = d.lam_fv(h_fv, lt_im, chained);
        let hyp_proof = d.lam_fv(i_fv, nat, hyp_body);
        let _ = hyp_pred;

        let bridge = d.lemma(p.count_range_congr_lt, &[f, g, m, hyp_proof]);
        let gnc_pp2m = gauss_neg_count(d, &p, pp, two, m);
        let cg_m = count_range_of(d, &p, g, m);

        let t2 = d.div(m, two);
        let disj_mm = d.lemma(p.gauss_count_ble_closed_form_disj, &[m, m]);
        let sub_eq = disj_to_sub_eq(d, &p, cg_m, m, t2, disj_mm);

        let sub_m_t2 = d.sub(m, t2);
        let result = d.trans(gnc_pp2m, cg_m, sub_m_t2, bridge, sub_eq);

        let stmt = d.eq(gnc_pp2m, sub_m_t2);
        (stmt, result)
    })?;
    Ok(())
}

/// `Nat.least_residue_injective_of_coprime : ∀ pp a k k', Lt 0 pp → Eq (gcd a
/// pp) 1 → Lt k pp → Lt k' pp → Eq (leastResidue pp a k) (leastResidue pp a
/// k') → Eq k k'`.
///
/// Piece 1 of the connecting theorem to `a^m mod pp` (ADR-0970/ADR-0985):
/// the least-residue map is injective on `[0, pp)` whenever `a` is coprime
/// to `pp`. Stated over bare positivity + coprimality rather than
/// primality directly — a caller in the classical Gauss's-lemma setting
/// (`pp` prime, `0 < a < pp`) supplies `gcd a pp = 1` via
/// `Nat.coprime_of_lt_prime` (`primes.rs`), which this theorem does not
/// need to know about.
///
/// Route (no case split): `leastResidue pp a k` unfolds definitionally to
/// `mod (mul a k) pp`. `mod_self_congr` (`group.rs`, exposed `pub(super)`
/// for this file) gives `modEq pp (a*k) (mod (a*k) pp)` and symmetrically
/// for `k'`; the hypothesis `heq` (defeq to `Eq (mod (a*k) pp) (mod (a*k')
/// pp)`) transports the second into `modEq pp (mod (a*k) pp) (a*k')` via a
/// custom `Eq.rec` motive (`fun x => modEq pp x (a*k')`); `mod_eq_trans`
/// chains that with the first to `modEq pp (a*k) (a*k')`; `Nat.mod_eq_cancel`
/// (`euler.rs`) cancels the shared coprime factor `a` to `modEq pp k k'`;
/// `mod_eq_of_mod_eq_rel` (`group.rs`) turns that back into `mod k pp = mod
/// k' pp`; `Nat.mod_eq_self_of_lt` collapses each side to `k`/`k'` using the
/// bound hypotheses, and a three-step `d.chain` closes `k = k'`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_least_residue_injective_of_coprime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.least_residue_injective_of_coprime, 4, &|d, v| {
        let (pp, a, k, k2) = (v[0], v[1], v[2], v[3]);
        let one = d.num(1);
        let zero = d.zero();

        let pos_pp_ty = d.lt(zero, pp);
        let gcd_ap = d.gcd(a, pp);
        let coprime_ty = d.eq(gcd_ap, one);
        let k_lt_ty = d.lt(k, pp);
        let k2_lt_ty = d.lt(k2, pp);
        let lr_k = least_residue(d, &p, pp, a, k);
        let lr_k2 = least_residue(d, &p, pp, a, k2);
        let heq_ty = d.eq(lr_k, lr_k2);
        let concl = d.eq(k, k2);

        let stmt = {
            let inner = d.arrow(heq_ty, concl);
            let inner2 = d.arrow(k2_lt_ty, inner);
            let inner3 = d.arrow(k_lt_ty, inner2);
            let inner4 = d.arrow(coprime_ty, inner3);
            d.arrow(pos_pp_ty, inner4)
        };

        let pos_pp_fv = d.fresh_fvar();
        let pos_pp = d.kernel().fvar(pos_pp_fv);
        let coprime_fv = d.fresh_fvar();
        let coprime = d.kernel().fvar(coprime_fv);
        let k_lt_fv = d.fresh_fvar();
        let k_lt = d.kernel().fvar(k_lt_fv);
        let k2_lt_fv = d.fresh_fvar();
        let k2_lt = d.kernel().fvar(k2_lt_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let ak = d.mul(a, k);
        let ak2 = d.mul(a, k2);
        let mod_ak_pp = d.modulo(ak, pp);
        let mod_ak2_pp = d.modulo(ak2, pp);

        // modEq pp ak (mod ak pp), modEq pp ak2 (mod ak2 pp)
        let modeq_ak = mod_self_congr(d, &p, pp, pos_pp, ak);
        let modeq_ak2 = mod_self_congr(d, &p, pp, pos_pp, ak2);

        // modEq pp (mod ak2 pp) ak2
        let modeq_ak2_symm = d.lemma(p.mod_eq_symm, &[pp, ak2, mod_ak2_pp, modeq_ak2]);

        // heq : Eq lr_k lr_k2, defeq to Eq mod_ak_pp mod_ak2_pp (leastResidue
        // unfolds definitionally, matching declare_gauss_residue_two_eq_double_of_lt's
        // own no-congruence-step idiom). Reversed: Eq mod_ak2_pp mod_ak_pp.
        let heq_rev = d.symm(lr_k, lr_k2, heq);

        // Transport modeq_ak2_symm's first argument along heq_rev:
        // modEq pp (mod ak2 pp) ak2  ~>  modEq pp (mod ak_pp) ak2
        let motive = d.eq_motive(mod_ak2_pp, &|d, x| d.mod_eq(pp, x, ak2));
        let modeq_akpp_ak2 = d.transport(mod_ak2_pp, motive, modeq_ak2_symm, mod_ak_pp, heq_rev);

        // modEq pp ak ak2, via mod_eq_trans through the shared mod_ak_pp point
        let modeq_ak_ak2 = d.lemma(
            p.mod_eq_trans,
            &[pp, ak, mod_ak_pp, ak2, modeq_ak, modeq_akpp_ak2],
        );

        // modEq pp k k2, cancelling the shared coprime factor a
        let modeq_k_k2 = d.lemma(p.mod_eq_cancel, &[pp, a, k, k2, coprime, modeq_ak_ak2]);

        // mod k pp = mod k2 pp
        let mod_eq_rel = mod_eq_of_mod_eq_rel(d, &p, pp, pos_pp, k, k2, modeq_k_k2);

        // mod k pp = k, mod k2 pp = k2
        let mod_eq_self_k = d.lemma(p.mod_eq_self_of_lt, &[k, pp, k_lt]);
        let mod_eq_self_k2 = d.lemma(p.mod_eq_self_of_lt, &[k2, pp, k2_lt]);

        let mod_k_pp = d.modulo(k, pp);
        let mod_k2_pp = d.modulo(k2, pp);
        let k_eq_mod_k = d.symm(mod_k_pp, k, mod_eq_self_k);

        let (_end, result) = d.chain(
            k,
            &[
                (mod_k_pp, k_eq_mod_k),
                (mod_k2_pp, mod_eq_rel),
                (k2, mod_eq_self_k2),
            ],
        );

        let with_heq = d.lam_fv(heq_fv, heq_ty, result);
        let with_k2 = d.lam_fv(k2_lt_fv, k2_lt_ty, with_heq);
        let with_k = d.lam_fv(k_lt_fv, k_lt_ty, with_k2);
        let with_coprime = d.lam_fv(coprime_fv, coprime_ty, with_k);
        let proof = d.lam_fv(pos_pp_fv, pos_pp_ty, with_coprime);

        (stmt, proof)
    })?;
    Ok(())
}

/// Everything this module declares, in dependency order. Goes last in
/// `build_nat_prelude`: it needs only `Nat.countRange`
/// (`declare_totient_all`), `Nat.mod_eq_self_of_lt` (`declare_size_all`, via
/// `binary.rs`), and `Nat.mod`/`Nat.mul`/`Nat.div`/`Nat.ble`, all far above.
/// Nothing needs it.
pub(super) fn declare_gauss_lemma_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_least_residue(d, p)?;
    declare_gauss_sign_neg(d, p)?;
    declare_gauss_neg_count(d, p)?;
    declare_gauss_residue_two_eq_double_of_lt(d, p)?;
    // a := 2, one representative of each nonzero residue class mod 8 among
    // small odd primes: 7 ≡ 7, 11 ≡ 3, 13 ≡ 5, 17 ≡ 1, 19 ≡ 3, 23 ≡ 7.
    // Values independently computed in Python (see this module's
    // `#[cfg(test)]` block) before being written here.
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_seven_two, 7, 2, 3, 2)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_eleven_two, 11, 2, 5, 3)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_thirteen_two, 13, 2, 6, 3)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_seventeen_two, 17, 2, 8, 4)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_nineteen_two, 19, 2, 9, 5)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_twentythree_two, 23, 2, 11, 6)?;
    // a := 3 at pp := 7, to confirm the count genuinely depends on `a`, not
    // only on `pp` (the a := 2 instance at the same prime gave 2, not 1).
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_seven_three, 7, 3, 3, 1)?;
    // The general closed form (ADR-0970/ADR-0985): needs only `Nat.countRange`
    // and the arithmetic/order lemmas already declared far above, plus
    // `gauss_residue_two_eq_double_of_lt` just above.
    declare_gauss_count_ble_closed_form_disj(d, p)?;
    declare_gauss_neg_count_two_closed_form(d, p)?;
    // Piece 1 of the connecting theorem (ADR-0970/ADR-0985): the
    // least-residue map's injectivity given only positivity + coprimality.
    declare_least_residue_injective_of_coprime(d, p)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Kernel, build_nat_prelude};

    /// The Python script whose output the concrete instance theorems above
    /// were transcribed from -- re-run here as a comment, not inherited,
    /// per this repository's standing rule that a "verified numerically"
    /// claim must be re-executed rather than trusted from a plan or a prior
    /// session.
    ///
    /// ```python
    /// def D(pp, a, m):
    ///     half = pp // 2
    ///     return sum(1 for k in range(1, m + 1) if (a * k) % pp > half)
    /// for pp in [7, 11, 13, 17, 19, 23]:
    ///     print(pp, pp % 8, D(pp, 2, (pp - 1) // 2))
    /// print(7, D(7, 3, 3))
    /// ```
    /// prints `7 7 2`, `11 3 3`, `13 5 3`, `17 1 4`, `19 3 5`, `23 7 6`, and
    /// `7 1` for the last line -- exactly the seven numbers this module's
    /// `declare_gauss_lemma_all` bakes in.
    #[test]
    fn gauss_neg_count_matches_an_independent_python_recomputation() {
        fn d_ref(pp: u32, a: u32, m: u32) -> u32 {
            let half = pp / 2;
            (1..=m).filter(|k| (a * k) % pp > half).count() as u32
        }
        assert_eq!(d_ref(7, 2, 3), 2);
        assert_eq!(d_ref(11, 2, 5), 3);
        assert_eq!(d_ref(13, 2, 6), 3);
        assert_eq!(d_ref(17, 2, 8), 4);
        assert_eq!(d_ref(19, 2, 9), 5);
        assert_eq!(d_ref(23, 2, 11), 6);
        assert_eq!(d_ref(7, 3, 3), 1);
    }

    /// The three definitions exist with the promised kind and the kernel's
    /// own reduction agrees with the Rust-side reference at a witness NOT
    /// among the landed theorems above (`pp := 5`, discriminating: `a := 2`
    /// gives count 1, `a := 1` gives count 0).
    #[test]
    fn gauss_definitions_compute_at_a_witness_outside_the_landed_table() {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut d = super::NatDev::new(&mut k, p);

        let five = d.num(5);
        let two = d.num(2);
        let one = d.num(1);
        let m = two; // (5-1)/2 = 2

        let count_a2 = gauss_neg_count(&mut d, &p, five, two, m);
        let expected_a2 = d.num(1);
        assert!(
            d.kernel().def_eq(count_a2, expected_a2),
            "gaussNegCount 5 2 2 must reduce to 1 (residues 2, 4; only 4 > 5/2=2)"
        );

        let count_a1 = gauss_neg_count(&mut d, &p, five, one, m);
        let expected_a1 = d.zero();
        assert!(
            d.kernel().def_eq(count_a1, expected_a1),
            "gaussNegCount 5 1 2 must reduce to 0 (residues 1, 2; neither exceeds 5/2=2)"
        );
        assert!(
            !d.kernel().def_eq(count_a1, expected_a2),
            "negative control: the two instances above must NOT collapse to the same value"
        );
    }

    /// The symbolic closed form (`gauss_neg_count_two_closed_form`),
    /// instantiated at `m := 3` (so `pp := succ(mul 2 3) = 7`), agrees with
    /// the independently landed `gauss_neg_count_seven_two` instance (`= 2`)
    /// -- both sides evaluated by the kernel's own reduction, not merely
    /// admitted. Per this repository's standing rule that a `Theorem`'s
    /// content must be spot-checked at concrete arguments, not just trusted
    /// because the kernel accepted the symbolic proof term.
    #[test]
    fn gauss_neg_count_two_closed_form_matches_the_landed_seven_two_instance() {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut d = super::NatDev::new(&mut k, p);

        let three = d.num(3);
        // The theorem itself applies at a concrete argument -- this is the
        // kernel-checked term, not merely a claim about it.
        let _proof = d.lemma(p.gauss_neg_count_two_closed_form, &[three]);

        let two = d.num(2);
        let mt = d.mul(two, three);
        let pp = d.succ(mt);
        let lhs = gauss_neg_count(&mut d, &p, pp, two, three);
        let t = d.div(three, two);
        let rhs = d.sub(three, t);
        let expected = d.num(2);
        assert!(
            d.kernel().def_eq(lhs, expected),
            "gaussNegCount (succ (mul 2 3)) 2 3 must reduce to 2 (matches gauss_neg_count_seven_two)"
        );
        assert!(
            d.kernel().def_eq(rhs, expected),
            "sub 3 (div 3 2) must reduce to 2"
        );
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "the closed form's two sides must agree at m := 3"
        );
    }
}
