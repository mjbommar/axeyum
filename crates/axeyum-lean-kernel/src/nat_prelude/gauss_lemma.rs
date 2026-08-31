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
use super::fermat_number_mirrors::pos_of_lt_add_left;
use super::group::{mod_eq_of_mod_eq_rel, mod_self_congr};
use super::helpers::{and_left, and_right, iff_reverse};
use super::ops::{NatDev, NatOps, bool_true_or_false};
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

/// `Nat.least_residue_ne_zero_of_coprime : ∀ pp a k, gcd a pp = 1 → 0 < k →
/// k < pp → 0 < leastResidue pp a k`.
///
/// The one lemma ADR-0990 flagged as genuinely absent while sizing piece 2
/// of the connecting theorem (the pairing lemma / signed-fold self-map): it
/// needs `leastResidue pp a k ≠ 0` so both of `gaussFold`'s branches
/// (`leastResidue pp a k` itself, or `pp - leastResidue pp a k`) land in
/// `[1, pp)`.
///
/// Route: assume `heq : leastResidue pp a k = 0` (defeq `mod (mul a k) pp =
/// 0`, matching `least_residue_injective_of_coprime`'s own no-congruence-
/// step idiom). `Nat.dvd_iff_mod_eq_zero`'s reverse direction turns that
/// into `pp ∣ (a*k)`; `Nat.gauss_lemma` (the EXISTING, unrelated
/// Euclid-cancellation theorem `gcd x y = 1 → x ∣ y*z → x ∣ z` — not this
/// module's target, see `nat_prelude/lcm.rs`) cancels the coprime factor
/// `a` (after flipping `gcd a pp = 1` to `gcd pp a = 1` via `gcd_comm`),
/// giving `pp ∣ k`. `Nat.le_of_dvd` (fed `0 < k`, defeq `1 ≤ k`) then gives
/// `pp ≤ k`, contradicting `k < pp` via `Nat.lt_of_le_of_lt`/`Nat.lt_irrefl`
/// — the identical three-lemma contradiction shape `bezout.rs`'s
/// `declare_euclid_lemma`-adjacent proof already uses at
/// `p.le_of_dvd`/`p.lt_of_le_of_lt`/`p.lt_irrefl`. `Nat.zero_lt_of_ne_zero`
/// closes the `Not (Eq lr zero) → Lt zero lr` step.
pub(super) fn declare_least_residue_ne_zero_of_coprime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.least_residue_ne_zero_of_coprime, 3, &|d, v| {
        let (pp, a, k) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let zero = d.zero();

        let gcd_ap = d.gcd(a, pp);
        let coprime_ty = d.eq(gcd_ap, one);
        let pos_k_ty = d.lt(zero, k);
        let k_lt_ty = d.lt(k, pp);
        let lr = least_residue(d, &p, pp, a, k);
        let concl = d.lt(zero, lr);

        let stmt = {
            let inner = d.arrow(k_lt_ty, concl);
            let inner2 = d.arrow(pos_k_ty, inner);
            d.arrow(coprime_ty, inner2)
        };

        let coprime_fv = d.fresh_fvar();
        let coprime = d.kernel().fvar(coprime_fv);
        let pos_k_fv = d.fresh_fvar();
        let pos_k = d.kernel().fvar(pos_k_fv);
        let k_lt_fv = d.fresh_fvar();
        let k_lt = d.kernel().fvar(k_lt_fv);

        // gcd pp a = 1, via gcd_comm (gauss_lemma needs the modulus first).
        let gcd_pa = d.gcd(pp, a);
        let comm = d.lemma(p.gcd_comm, &[a, pp]); // Eq (gcd a pp) (gcd pp a)
        let comm_rev = d.symm(gcd_ap, gcd_pa, comm); // Eq (gcd pp a) (gcd a pp)
        let coprime_pa = d.trans(gcd_pa, gcd_ap, one, comm_rev, coprime); // Eq (gcd pp a) one

        // Assume heq : Eq lr zero (defeq Eq (mod (mul a k) pp) zero).
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = d.eq(lr, zero);

        let ak = d.mul(a, k);
        let mod_ak_pp = d.modulo(ak, pp);
        let dvd_ty = d.dvd(pp, ak);
        let eq_ty = d.eq(mod_ak_pp, zero);
        let iff_pf = d.lemma(p.dvd_iff_mod_eq_zero, &[pp, ak]); // Iff dvd_ty eq_ty
        let rev = iff_reverse(d, dvd_ty, eq_ty, iff_pf); // eq_ty -> dvd_ty
        let dvd_pp_ak = d.apply(rev, &[heq]); // dvd pp ak, via defeq heq : eq_ty

        let dvd_pp_k = d.lemma(p.gauss_lemma, &[pp, a, k, coprime_pa, dvd_pp_ak]); // dvd pp k

        let le_pp_k = d.lemma(p.le_of_dvd, &[pp, k, pos_k, dvd_pp_k]); // Le pp k
        let lt_pp_pp = d.lemma(p.lt_of_le_of_lt, &[pp, k, pp, le_pp_k, k_lt]); // Lt pp pp
        let lt_irrefl_pp = d.lemma(p.lt_irrefl, &[pp]);
        let false_proof = d.apply(lt_irrefl_pp, &[lt_pp_pp]);

        let not_heq = d.lam_fv(heq_fv, heq_ty, false_proof); // Not (Eq lr zero)
        let concl_pf = d.lemma(p.zero_lt_of_ne_zero, &[lr, not_heq]); // Lt zero lr

        let with_k_lt = d.lam_fv(k_lt_fv, k_lt_ty, concl_pf);
        let with_pos_k = d.lam_fv(pos_k_fv, pos_k_ty, with_k_lt);
        let proof = d.lam_fv(coprime_fv, coprime_ty, with_pos_k);
        (stmt, proof)
    })?;
    Ok(())
}

/// Delta height for `Nat.gaussFold`: strictly above `Nat.gaussSignNeg`'s
/// (33) and `Nat.leastResidue`'s (32).
const GAUSS_FOLD_HEIGHT: u16 = 34;

/// `Nat.gaussFold(pp, a, k)`.
pub(super) fn gauss_fold(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.gauss_fold, &[pp, a, k])
}

/// `Nat.gaussFold : Nat → Nat → Nat → Nat := fun pp a k => if gaussSignNeg
/// pp a k then sub pp (leastResidue pp a k) else leastResidue pp a k`.
///
/// Not recursive: a plain triple-lambda over `Bool.rec` (`bool_select_nat`),
/// composing two already-declared primitives, the same shape
/// `declare_least_residue` uses.
pub(super) fn declare_gauss_fold(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let test = gauss_sign_neg(d, &p, pp, a, k);
    let lr = least_residue(d, &p, pp, a, k);
    let neg_val = d.sub(pp, lr);
    let body = d.bool_select_nat(test, neg_val, lr);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_a = d.lam_fv(a_fv, nat, with_k);
        d.lam_fv(pp_fv, nat, with_a)
    };
    let ty = {
        let inner = d.arrow(nat, nat);
        let mid = d.arrow(nat, inner);
        d.arrow(nat, mid)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.gauss_fold,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(GAUSS_FOLD_HEIGHT),
    })
}

/// `h : Eq Bool a b ⊢ Eq Nat (body a) (body b)` — private per-file copy of
/// the same shape `totient.rs`/`count_range_permute.rs`/`perfect.rs` each
/// already carry (see their doc comments for why this follows the existing
/// per-file-copy convention rather than a new shared one).
fn bool_congr_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = body(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = body(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `h : Eq test bconst ⊢ Eq (gaussFold pp a k) (branch value at bconst)` —
/// the RHS ι-reduces once `bconst` is a literal (`true`/`false`), giving (by
/// defeq) the branch value without a separate reduction step, matching this
/// file's existing no-congruence-step idiom (`declare_least_residue_
/// injective_of_coprime`'s own `heq` handling). The caller supplies `bconst`
/// already knowing which branch value it names.
fn fold_eq_branch(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    k: ExprId,
    bconst: ExprId,
    h: ExprId,
) -> ExprId {
    let test = gauss_sign_neg(d, p, pp, a, k);
    let lr = least_residue(d, p, pp, a, k);
    let neg = d.sub(pp, lr);
    bool_congr_nat(d, test, bconst, h, &|d, x| d.bool_select_nat(x, neg, lr))
}

/// Non-dependent `Or.rec` (private per-file copy; see `add_basics.rs`'s
/// module doc for why this follows the existing convention).
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `False.rec` into `goal` (private per-file copy; see `add_basics.rs`'s
/// module doc for why this follows the existing convention).
fn absurd(d: &mut NatDev<'_>, p: &NatPrelude, goal: ExprId, contradiction: ExprId) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// `Lt x y ⊢ Le x y` — weaken a strict bound (`Nat.lt` unfolds definitionally
/// to `Le (succ x) y`, so this is `le_trans` through `le_succ`, no induction).
fn le_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, y: ExprId, hlt: ExprId) -> ExprId {
    let p = *p;
    let sx = d.succ(x);
    let le_x_sx = d.lemma(p.le_succ, &[x]);
    d.lemma(p.le_trans, &[x, sx, y, le_x_sx, hlt])
}

/// `Eq (mul 2 m) (add m m)` — `Nat.mul` recurses on its RIGHT argument, so
/// `mul 2 m` is stuck for symbolic `m`; built via `succ_mul` (`mul (succ
/// one) m = add (mul one m) m`) plus `one_mul`, the same route
/// `binary_rec.rs`'s `declare_halving_arithmetic` uses inline for
/// `lt_two_mul_of_pos`.
fn two_mul_eq_add(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let mul_one_m = d.mul(one, m);
    let add_mul_one_m_m = d.add(mul_one_m, m);
    let succ_mul_eq = d.lemma(p.succ_mul, &[one, m]); // Eq (mul (succ one) m) add_mul_one_m_m
    let one_mul_eq = d.lemma(p.one_mul, &[m]); // Eq mul_one_m m
    let congr_step = d.congr(mul_one_m, m, one_mul_eq, &|d, x| d.add(x, m));
    let mul_two_m = d.mul(two, m);
    let add_m_m = d.add(m, m);
    let (_e, result) = d.chain(
        mul_two_m,
        &[(add_mul_one_m_m, succ_mul_eq), (add_m_m, congr_step)],
    );
    result
}

/// `Lt a b ⊢ Lt zero (sub b a)` — a per-file copy of `dist_more2.rs`'s
/// private `sub_pos_of_lt` (that one is not `pub(super)`, so not
/// importable): from `Lt a b`, `sub_add_cancel` gives `b = add (sub b a)
/// a`, rewritten via `add_comm` to `b = add a (sub b a)`; transporting
/// `hlt` along that equation gives `Lt a (add a (sub b a))`, and
/// `pos_of_lt_add_left` finishes.
fn sub_pos_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let p = *p;
    let h_le = le_of_lt(d, &p, a, b, hlt);
    let sub_ba = d.sub(b, a);
    let h_cancel = d.lemma(p.sub_add_cancel, &[a, b, h_le]); // Eq (add sub_ba a) b
    let add_a_subba = d.add(a, sub_ba);
    let add_subba_a = d.add(sub_ba, a);
    let h_comm = d.lemma(p.add_comm, &[sub_ba, a]); // Eq add_subba_a add_a_subba
    let h_comm_rev = d.symm(add_subba_a, add_a_subba, h_comm); // Eq add_a_subba add_subba_a
    let h_eq = d.trans(add_a_subba, add_subba_a, b, h_comm_rev, h_cancel); // Eq add_a_subba b
    let h_eq_rev = d.symm(add_a_subba, b, h_eq); // Eq b add_a_subba
    let motive = d.eq_motive(b, &|d, x| d.lt(a, x));
    let hlt2 = d.transport(b, motive, hlt, add_a_subba, h_eq_rev); // Lt a (add a sub_ba)
    pos_of_lt_add_left(d, &p, a, sub_ba, hlt2)
}

/// Same-sign, IDENTITY branch (`test_k = test_k' = false`): `heq` transports
/// directly to `Eq (leastResidue pp a k) (leastResidue pp a k')`, closed by
/// `least_residue_injective_of_coprime` (piece 1).
#[allow(clippy::too_many_arguments)]
fn same_sign_identity(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    k: ExprId,
    k2: ExprId,
    coprime: ExprId,
    pos_pp: ExprId,
    lt_k_pp: ExprId,
    lt_k2_pp: ExprId,
    h_k: ExprId,
    h_k2: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let false_ = d.bool_false();
    let lr_k = least_residue(d, &p, pp, a, k);
    let lr_k2 = least_residue(d, &p, pp, a, k2);
    let fold_k = gauss_fold(d, &p, pp, a, k);
    let fold_k2 = gauss_fold(d, &p, pp, a, k2);
    let eq_k = fold_eq_branch(d, &p, pp, a, k, false_, h_k); // Eq fold_k lr_k
    let eq_k2 = fold_eq_branch(d, &p, pp, a, k2, false_, h_k2); // Eq fold_k2 lr_k2
    let eq_k_rev = d.symm(fold_k, lr_k, eq_k); // Eq lr_k fold_k
    let (_e, lr_eq) = d.chain(lr_k, &[(fold_k, eq_k_rev), (fold_k2, heq), (lr_k2, eq_k2)]);
    d.lemma(
        p.least_residue_injective_of_coprime,
        &[pp, a, k, k2, pos_pp, coprime, lt_k_pp, lt_k2_pp, lr_eq],
    )
}

/// Same-sign, NEGATIVE branch (`test_k = test_k' = true`): `heq` transports
/// to `Eq (sub pp lr_k) (sub pp lr_k')`; `add_sub_cancel_of_le` at each side
/// plus `add_right_cancel` recovers `Eq lr_k lr_k'` (no dedicated
/// subtraction-cancellation lemma exists in the tree, per ADR-0990), then
/// `least_residue_injective_of_coprime` (piece 1) closes it.
#[allow(clippy::too_many_arguments)]
fn same_sign_negative(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    k: ExprId,
    k2: ExprId,
    coprime: ExprId,
    pos_pp: ExprId,
    lt_k_pp: ExprId,
    lt_k2_pp: ExprId,
    h_k: ExprId,
    h_k2: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let true_ = d.bool_true();
    let lr_k = least_residue(d, &p, pp, a, k);
    let lr_k2 = least_residue(d, &p, pp, a, k2);
    let neg_k = d.sub(pp, lr_k);
    let neg_k2 = d.sub(pp, lr_k2);
    let fold_k = gauss_fold(d, &p, pp, a, k);
    let fold_k2 = gauss_fold(d, &p, pp, a, k2);
    let eq_k = fold_eq_branch(d, &p, pp, a, k, true_, h_k); // Eq fold_k neg_k
    let eq_k2 = fold_eq_branch(d, &p, pp, a, k2, true_, h_k2); // Eq fold_k2 neg_k2
    let eq_k_rev = d.symm(fold_k, neg_k, eq_k); // Eq neg_k fold_k
    let (_e, neg_eq) = d.chain(
        neg_k,
        &[(fold_k, eq_k_rev), (fold_k2, heq), (neg_k2, eq_k2)],
    );
    // neg_eq : Eq neg_k neg_k2, i.e. Eq (sub pp lr_k) (sub pp lr_k2).

    let ak = d.mul(a, k);
    let ak2 = d.mul(a, k2);
    let lr_k_lt_pp = d.lemma(p.mod_lt, &[ak, pp, pos_pp]);
    let lr_k2_lt_pp = d.lemma(p.mod_lt, &[ak2, pp, pos_pp]);
    let le_lr_k_pp = le_of_lt(d, &p, lr_k, pp, lr_k_lt_pp);
    let le_lr_k2_pp = le_of_lt(d, &p, lr_k2, pp, lr_k2_lt_pp);

    let cancel_k = d.lemma(p.add_sub_cancel_of_le, &[lr_k, pp, le_lr_k_pp]); // Eq (add lr_k neg_k) pp
    let cancel_k2 = d.lemma(p.add_sub_cancel_of_le, &[lr_k2, pp, le_lr_k2_pp]); // Eq (add lr_k2 neg_k2) pp

    let add_lr_k_negk = d.add(lr_k, neg_k);
    let add_lr_k_negk2 = d.add(lr_k, neg_k2);
    let congr1 = d.congr(neg_k, neg_k2, neg_eq, &|d, x| d.add(lr_k, x)); // Eq add_lr_k_negk add_lr_k_negk2
    let congr1_rev = d.symm(add_lr_k_negk, add_lr_k_negk2, congr1); // Eq add_lr_k_negk2 add_lr_k_negk
    let step_a = d.trans(add_lr_k_negk2, add_lr_k_negk, pp, congr1_rev, cancel_k); // Eq add_lr_k_negk2 pp

    let add_lr_k2_negk2 = d.add(lr_k2, neg_k2);
    let cancel_k2_rev = d.symm(add_lr_k2_negk2, pp, cancel_k2); // Eq pp add_lr_k2_negk2
    let step_b = d.trans(add_lr_k_negk2, pp, add_lr_k2_negk2, step_a, cancel_k2_rev);
    // step_b : Eq (add lr_k neg_k2) (add lr_k2 neg_k2) -- same second addend.
    let lr_eq = d.lemma(p.add_right_cancel, &[lr_k, lr_k2, neg_k2, step_b]); // Eq lr_k lr_k2

    d.lemma(
        p.least_residue_injective_of_coprime,
        &[pp, a, k, k2, pos_pp, coprime, lt_k_pp, lt_k2_pp, lr_eq],
    )
}

/// Opposite-sign branch (`k` negative, `j` not): impossible on `[1, m]`.
/// `sub_eq : Eq (sub pp (leastResidue pp a k)) (leastResidue pp a j)`
/// forces `leastResidue pp a k + leastResidue pp a j = pp`
/// (`add_sub_cancel_of_le`), hence `a*(k+j) ≡ 0 [pp]` (`mod_eq_add` +
/// `mod_eq_zero_of_dvd` at `pp ∣ pp`), hence `k+j ≡ 0 [pp]`
/// (`mod_eq_cancel`, coprimality). But `k+j ≤ 2m < pp` (both indices `≤ m`),
/// so `k+j = 0` outright (`mod_eq_self_of_lt`) — contradicting `0 < k`
/// (`add_eq_zero` + `lt_irrefl`).
#[allow(clippy::too_many_arguments)]
fn opposite_sign_vacuous(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    mul2m: ExprId,
    m: ExprId,
    a: ExprId,
    coprime: ExprId,
    pos_pp: ExprId,
    k: ExprId,
    pos_k: ExprId,
    le_k_m: ExprId,
    j: ExprId,
    le_j_m: ExprId,
    sub_eq: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let lr_k = least_residue(d, &p, pp, a, k);
    let lr_j = least_residue(d, &p, pp, a, j);
    let ak = d.mul(a, k);
    let aj = d.mul(a, j);

    let lr_k_lt_pp = d.lemma(p.mod_lt, &[ak, pp, pos_pp]);
    let le_lr_k_pp = le_of_lt(d, &p, lr_k, pp, lr_k_lt_pp);
    let cancel_k = d.lemma(p.add_sub_cancel_of_le, &[lr_k, pp, le_lr_k_pp]); // Eq (add lr_k (sub pp lr_k)) pp

    let sub_pp_lr_k = d.sub(pp, lr_k);
    let add_lr_k_subk = d.add(lr_k, sub_pp_lr_k);
    let add_lr_k_lrj = d.add(lr_k, lr_j);
    let congr_step = d.congr(sub_pp_lr_k, lr_j, sub_eq, &|d, x| d.add(lr_k, x)); // Eq add_lr_k_subk add_lr_k_lrj
    let congr_step_rev = d.symm(add_lr_k_subk, add_lr_k_lrj, congr_step);
    let sum_eq_pp = d.trans(add_lr_k_lrj, add_lr_k_subk, pp, congr_step_rev, cancel_k); // Eq add_lr_k_lrj pp

    let modeq_ak = mod_self_congr(d, &p, pp, pos_pp, ak); // modEq pp ak lr_k (defeq)
    let modeq_aj = mod_self_congr(d, &p, pp, pos_pp, aj); // modEq pp aj lr_j
    let modeq_sum = d.lemma(p.mod_eq_add, &[pp, ak, lr_k, aj, lr_j, modeq_ak, modeq_aj]); // modEq pp (ak+aj) add_lr_k_lrj

    let add_ak_aj = d.add(ak, aj);
    let modeq_transported = {
        let motive = d.eq_motive(add_lr_k_lrj, &|d, x| d.mod_eq(pp, add_ak_aj, x));
        d.transport(add_lr_k_lrj, motive, modeq_sum, pp, sum_eq_pp)
    }; // modEq pp (ak+aj) pp

    let dvd_pp_pp = d.lemma(p.dvd_refl, &[pp]);
    let modeq_pp_zero = d.lemma(p.mod_eq_zero_of_dvd, &[pp, pp, dvd_pp_pp]); // modEq pp pp zero
    let modeq_akaj_zero = d.lemma(
        p.mod_eq_trans,
        &[pp, add_ak_aj, pp, zero, modeq_transported, modeq_pp_zero],
    ); // modEq pp (ak+aj) zero

    let k_plus_j = d.add(k, j);
    let a_kj = d.mul(a, k_plus_j);
    let distrib = d.lemma(p.left_distrib, &[a, k, j]); // Eq a_kj add_ak_aj
    let distrib_rev = d.symm(a_kj, add_ak_aj, distrib);
    let modeq_akj_zero = {
        let motive = d.eq_motive(add_ak_aj, &|d, x| d.mod_eq(pp, x, zero));
        d.transport(add_ak_aj, motive, modeq_akaj_zero, a_kj, distrib_rev)
    }; // modEq pp a_kj zero

    let a_zero = d.mul(a, zero);
    let mul_zero_pf = d.lemma(p.mul_zero, &[a]); // Eq a_zero zero
    let mul_zero_rev = d.symm(a_zero, zero, mul_zero_pf); // Eq zero a_zero
    let modeq_akj_azero = {
        let motive = d.eq_motive(zero, &|d, x| d.mod_eq(pp, a_kj, x));
        d.transport(zero, motive, modeq_akj_zero, a_zero, mul_zero_rev)
    }; // modEq pp a_kj a_zero

    let modeq_kj_zero = d.lemma(
        p.mod_eq_cancel,
        &[pp, a, k_plus_j, zero, coprime, modeq_akj_azero],
    );

    // k + j ≤ m + m = mul 2 m < pp.
    let add_k_m = d.add(k, m);
    let add_m_m = d.add(m, m);
    let le1 = d.lemma(p.add_le_add_left, &[k, j, m, le_j_m]); // Le (add k j)(add k m)
    let le2 = d.lemma(p.add_le_add_right, &[m, k, m, le_k_m]); // Le (add k m)(add m m)
    let le_kj_mm = d.lemma(p.le_trans, &[k_plus_j, add_k_m, add_m_m, le1, le2]); // Le k_plus_j add_m_m

    let two_mul_m_eq_mm = two_mul_eq_add(d, &p, m); // Eq mul2m add_m_m
    let le_kj_mul2m = {
        let motive = d.eq_motive(add_m_m, &|d, x| d.le(k_plus_j, x));
        let h = d.symm(mul2m, add_m_m, two_mul_m_eq_mm); // Eq add_m_m mul2m
        d.transport(add_m_m, motive, le_kj_mm, mul2m, h)
    }; // Le k_plus_j mul2m

    let lt_kj_pp = d.lemma(p.lt_succ_of_le, &[k_plus_j, mul2m, le_kj_mul2m]); // Lt k_plus_j pp

    let mod_eq_rel = mod_eq_of_mod_eq_rel(d, &p, pp, pos_pp, k_plus_j, zero, modeq_kj_zero);
    let mod_eq_self_kj = d.lemma(p.mod_eq_self_of_lt, &[k_plus_j, pp, lt_kj_pp]); // Eq (mod k_plus_j pp) k_plus_j
    let zero_mod_pf = d.lemma(p.zero_mod, &[pp]); // Eq (mod zero pp) zero

    let mod_kj_pp = d.modulo(k_plus_j, pp);
    let mod_zero_pp = d.modulo(zero, pp);
    let kj_eq_mod_kj = d.symm(mod_kj_pp, k_plus_j, mod_eq_self_kj); // Eq k_plus_j (mod k_plus_j pp)
    let (_e, kj_eq_zero) = d.chain(
        k_plus_j,
        &[
            (mod_kj_pp, kj_eq_mod_kj),
            (mod_zero_pp, mod_eq_rel),
            (zero, zero_mod_pf),
        ],
    ); // Eq k_plus_j zero

    let and_pf = d.lemma(p.add_eq_zero, &[k, j, kj_eq_zero]); // And (Eq k zero)(Eq j zero)
    let k_zero_ty = d.eq(k, zero);
    let j_zero_ty = d.eq(j, zero);
    let k_eq_zero = and_left(d, k_zero_ty, j_zero_ty, and_pf);

    let motive_pos = d.eq_motive(k, &|d, x| d.lt(zero, x));
    let pos_zero = d.transport(k, motive_pos, pos_k, zero, k_eq_zero); // Lt zero zero
    let irrefl = d.lemma(p.lt_irrefl, &[zero]);
    d.apply(irrefl, &[pos_zero])
}

/// `Nat.gauss_fold_injective_of_coprime : ∀ m a k k', gcd a (succ (mul 2 m))
///   = 1 → 0 < k → Le k m → 0 < k' → Le k' m → gaussFold (succ (mul 2 m)) a
///   k = gaussFold (succ (mul 2 m)) a k' → k = k'`.
///
/// Piece 2 of the connecting theorem (ADR-0970/ADR-0985/ADR-0990). By cases
/// on `gaussSignNeg pp a k`/`gaussSignNeg pp a k'` (`bool_true_or_false`,
/// nested): same-sign closes via [`same_sign_identity`]/
/// [`same_sign_negative`]; opposite-sign is vacuous via
/// [`opposite_sign_vacuous`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gauss_fold_injective_of_coprime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_fold_injective_of_coprime, 4, &|d, v| {
        let (m, a, k, k2) = (v[0], v[1], v[2], v[3]);
        let two = d.num(2);
        let one = d.num(1);
        let zero = d.zero();
        let mul2m = d.mul(two, m);
        let pp = d.succ(mul2m);

        let gcd_a_pp = d.gcd(a, pp);
        let coprime_ty = d.eq(gcd_a_pp, one);
        let pos_k_ty = d.lt(zero, k);
        let le_k_m_ty = d.le(k, m);
        let pos_k2_ty = d.lt(zero, k2);
        let le_k2_m_ty = d.le(k2, m);
        let fold_k = gauss_fold(d, &p, pp, a, k);
        let fold_k2 = gauss_fold(d, &p, pp, a, k2);
        let heq_ty = d.eq(fold_k, fold_k2);
        let concl = d.eq(k, k2);

        let stmt = {
            let inner = d.arrow(heq_ty, concl);
            let inner2 = d.arrow(le_k2_m_ty, inner);
            let inner3 = d.arrow(pos_k2_ty, inner2);
            let inner4 = d.arrow(le_k_m_ty, inner3);
            let inner5 = d.arrow(pos_k_ty, inner4);
            d.arrow(coprime_ty, inner5)
        };

        let coprime_fv = d.fresh_fvar();
        let coprime = d.kernel().fvar(coprime_fv);
        let pos_k_fv = d.fresh_fvar();
        let pos_k = d.kernel().fvar(pos_k_fv);
        let le_k_m_fv = d.fresh_fvar();
        let le_k_m = d.kernel().fvar(le_k_m_fv);
        let pos_k2_fv = d.fresh_fvar();
        let pos_k2 = d.kernel().fvar(pos_k2_fv);
        let le_k2_m_fv = d.fresh_fvar();
        let le_k2_m = d.kernel().fvar(le_k2_m_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let pos_pp = d.zero_lt_succ(mul2m);

        // k, k2 < pp: from `Le k m`/`Le k2 m` and `Lt m pp` (via
        // `lt_two_mul_of_pos` at `0 < m`, itself from `0 < k ≤ m`).
        let pos_m = d.lemma(p.lt_of_lt_of_le, &[zero, k, m, pos_k, le_k_m]); // Lt zero m
        let lt_m_2m = d.lemma(p.lt_two_mul_of_pos, &[m, pos_m]); // Lt m mul2m
        let le_2m_pp = d.lemma(p.le_succ, &[mul2m]); // Le mul2m pp
        let lt_m_pp = d.lemma(p.lt_of_lt_of_le, &[m, mul2m, pp, lt_m_2m, le_2m_pp]); // Lt m pp
        let lt_k_pp = d.lemma(p.lt_of_le_of_lt, &[k, m, pp, le_k_m, lt_m_pp]); // Lt k pp
        let lt_k2_pp = d.lemma(p.lt_of_le_of_lt, &[k2, m, pp, le_k2_m, lt_m_pp]); // Lt k2 pp

        let test_k = gauss_sign_neg(d, &p, pp, a, k);
        let test_k2 = gauss_sign_neg(d, &p, pp, a, k2);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let ty_k_true = d.bool_eq(test_k, true_);
        let ty_k_false = d.bool_eq(test_k, false_);
        let ty_k2_true = d.bool_eq(test_k2, true_);
        let ty_k2_false = d.bool_eq(test_k2, false_);

        let case_k = bool_true_or_false(d, &p, test_k);
        let case_k2 = bool_true_or_false(d, &p, test_k2);

        // Outer branch: test_k = true (k negative).
        let minor_k_true = {
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);

            // Inner branch: test_k2 = true (k2 also negative) -- same-sign.
            let inner_true = {
                let hk2_fv = d.fresh_fvar();
                let hk2 = d.kernel().fvar(hk2_fv);
                let body = same_sign_negative(
                    d, &p, pp, a, k, k2, coprime, pos_pp, lt_k_pp, lt_k2_pp, hk, hk2, heq,
                );
                d.lam_fv(hk2_fv, ty_k2_true, body)
            };
            // Inner branch: test_k2 = false (k2 not negative) -- opposite-sign.
            let inner_false = {
                let hk2_fv = d.fresh_fvar();
                let hk2 = d.kernel().fvar(hk2_fv);
                // sub_eq : Eq (sub pp (leastResidue pp a k)) (leastResidue pp a k2)
                let fold_k = gauss_fold(d, &p, pp, a, k);
                let fold_k2 = gauss_fold(d, &p, pp, a, k2);
                let lr_k = least_residue(d, &p, pp, a, k);
                let neg_k = d.sub(pp, lr_k);
                let lr_k2 = least_residue(d, &p, pp, a, k2);
                let eq_k = fold_eq_branch(d, &p, pp, a, k, true_, hk); // Eq fold_k neg_k
                let eq_k2 = fold_eq_branch(d, &p, pp, a, k2, false_, hk2); // Eq fold_k2 lr_k2
                let eq_k_rev = d.symm(fold_k, neg_k, eq_k);
                let (_e, sub_eq) =
                    d.chain(neg_k, &[(fold_k, eq_k_rev), (fold_k2, heq), (lr_k2, eq_k2)]);
                let false_pf = opposite_sign_vacuous(
                    d, &p, pp, mul2m, m, a, coprime, pos_pp, k, pos_k, le_k_m, k2, le_k2_m, sub_eq,
                );
                let body = absurd(d, &p, concl, false_pf);
                d.lam_fv(hk2_fv, ty_k2_false, body)
            };
            let body = or_elim(
                d,
                &p,
                ty_k2_true,
                ty_k2_false,
                concl,
                inner_true,
                inner_false,
                case_k2,
            );
            d.lam_fv(hk_fv, ty_k_true, body)
        };

        // Outer branch: test_k = false (k not negative).
        let minor_k_false = {
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);

            // Inner branch: test_k2 = true (k2 negative) -- opposite-sign,
            // mirrored (k2 plays the "negative" role).
            let inner_true = {
                let hk2_fv = d.fresh_fvar();
                let hk2 = d.kernel().fvar(hk2_fv);
                let fold_k = gauss_fold(d, &p, pp, a, k);
                let fold_k2 = gauss_fold(d, &p, pp, a, k2);
                let lr_k = least_residue(d, &p, pp, a, k);
                let lr_k2 = least_residue(d, &p, pp, a, k2);
                let neg_k2 = d.sub(pp, lr_k2);
                let eq_k = fold_eq_branch(d, &p, pp, a, k, false_, hk); // Eq fold_k lr_k
                let eq_k2 = fold_eq_branch(d, &p, pp, a, k2, true_, hk2); // Eq fold_k2 neg_k2
                let eq_k_rev = d.symm(fold_k, lr_k, eq_k);
                let (_e, heq_k2_neg) =
                    d.chain(lr_k, &[(fold_k, eq_k_rev), (fold_k2, heq), (neg_k2, eq_k2)]);
                // heq_k2_neg : Eq lr_k neg_k2. Need Eq (sub pp lr_k2) lr_k for
                // `opposite_sign_vacuous`'s `sub_eq` shape (k2 negative, k
                // playing the "j" role): symm gives Eq neg_k2 lr_k.
                let sub_eq = d.symm(lr_k, neg_k2, heq_k2_neg);
                let false_pf = opposite_sign_vacuous(
                    d, &p, pp, mul2m, m, a, coprime, pos_pp, k2, pos_k2, le_k2_m, k, le_k_m, sub_eq,
                );
                let body = absurd(d, &p, concl, false_pf);
                d.lam_fv(hk2_fv, ty_k2_true, body)
            };
            // Inner branch: test_k2 = false (k2 not negative) -- same-sign identity.
            let inner_false = {
                let hk2_fv = d.fresh_fvar();
                let hk2 = d.kernel().fvar(hk2_fv);
                let body = same_sign_identity(
                    d, &p, pp, a, k, k2, coprime, pos_pp, lt_k_pp, lt_k2_pp, hk, hk2, heq,
                );
                d.lam_fv(hk2_fv, ty_k2_false, body)
            };
            let body = or_elim(
                d,
                &p,
                ty_k2_true,
                ty_k2_false,
                concl,
                inner_true,
                inner_false,
                case_k2,
            );
            d.lam_fv(hk_fv, ty_k_false, body)
        };

        let result = or_elim(
            d,
            &p,
            ty_k_true,
            ty_k_false,
            concl,
            minor_k_true,
            minor_k_false,
            case_k,
        );

        let with_heq = d.lam_fv(heq_fv, heq_ty, result);
        let with_le_k2 = d.lam_fv(le_k2_m_fv, le_k2_m_ty, with_heq);
        let with_pos_k2 = d.lam_fv(pos_k2_fv, pos_k2_ty, with_le_k2);
        let with_le_k = d.lam_fv(le_k_m_fv, le_k_m_ty, with_pos_k2);
        let with_pos_k = d.lam_fv(pos_k_fv, pos_k_ty, with_le_k);
        let proof = d.lam_fv(coprime_fv, coprime_ty, with_pos_k);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.div_succ_two_mul_eq_self : ∀ m, Eq (div (succ (mul 2 m)) 2) m`.
///
/// Route (ADR-1015): `add_mul_div_left` at `(x, z, y) := (1, m, 2)` gives
/// `Eq (div (add 1 (mul 2 m)) 2) (add (div 1 2) m)`; `div 1 2 = 0` closes by
/// the kernel's own unary reduction (`Eq.refl`, well under the numeral cost
/// cliff), and `zero_add` collapses the RHS to `m`. The LHS needs `add 1
/// (mul 2 m)` bridged to `pp`'s actual `succ (mul 2 m)` shape: `Nat.add`
/// recurses on its RIGHT argument, so `add 1 (mul 2 m)` (literal on the
/// LEFT, `mul 2 m` symbolic on the RIGHT) is stuck, but `add_comm` flips it
/// to `add (mul 2 m) 1`, whose right argument is now the literal `1` --
/// `add (mul 2 m) 1` IS defeq `succ (mul 2 m)` by two iota steps
/// (`add x (succ zero) = succ (add x zero) = succ x`), regardless of `mul 2
/// m` itself being stuck (it is carried along unreduced, not matched on).
pub(super) fn declare_div_succ_two_mul_eq_self(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.div_succ_two_mul_eq_self, 1, &|d, v| {
        let m = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();
        let mul2m = d.mul(two, m);
        let pp = d.succ(mul2m);

        let div_pp_two = d.div(pp, two);
        let concl = d.eq(div_pp_two, m);

        let pos_two = d.lemma(p.zero_lt_succ, &[one]); // Lt zero (succ one) ~ Lt zero two

        // add_mul_div_left(1, m, 2, pos_two) : Eq (div (add 1 mul2m) 2) (add (div 1 2) m)
        let step1 = d.lemma(p.add_mul_div_left, &[one, m, two, pos_two]);

        let add_one_mul2m = d.add(one, mul2m);
        let div_add_one_mul2m_two = d.div(add_one_mul2m, two);
        let div_one_two = d.div(one, two);
        let add_div12_m = d.add(div_one_two, m);

        // add_comm(1, mul2m) : Eq (add 1 mul2m) (add mul2m 1)
        let add_comm_pf = d.lemma(p.add_comm, &[one, mul2m]);
        let add_mul2m_one = d.add(mul2m, one);
        // add(mul2m, 1) is defeq succ(mul2m) = pp (literal 1 on the right).
        let add_mul2m_one_eq_pp = d.refl(pp);
        let add_one_mul2m_eq_pp = d.trans(
            add_one_mul2m,
            add_mul2m_one,
            pp,
            add_comm_pf,
            add_mul2m_one_eq_pp,
        );

        // Rewrite div(add 1 mul2m, 2) to div(pp, 2), then take the reverse
        // direction to anchor the chain at div_pp_two.
        let congr_lhs = d.congr(add_one_mul2m, pp, add_one_mul2m_eq_pp, &|d, x| {
            d.div(x, two)
        });
        let lhs_rewrite = d.symm(div_add_one_mul2m_two, div_pp_two, congr_lhs);
        // lhs_rewrite : Eq div_pp_two div_add_one_mul2m_two

        // div 1 2 = 0, by the kernel's own reduction.
        let div_one_two_eq_zero = d.refl(zero);
        let congr_rhs = d.congr(div_one_two, zero, div_one_two_eq_zero, &|d, x| d.add(x, m));
        let add_zero_m = d.add(zero, m);
        // congr_rhs : Eq add_div12_m add_zero_m

        let zero_add_m = d.lemma(p.zero_add, &[m]); // Eq (add zero m) m

        let (_e, proof) = d.chain(
            div_pp_two,
            &[
                (div_add_one_mul2m_two, lhs_rewrite),
                (add_div12_m, step1),
                (add_zero_m, congr_rhs),
                (m, zero_add_m),
            ],
        );

        (concl, proof)
    })?;
    Ok(())
}

/// `Nat.gauss_fold_in_range : ∀ m a k, gcd a (succ (mul 2 m)) = 1 → 0 < k →
///   Le k m → And (0 < gaussFold (succ (mul 2 m)) a k) (Le (gaussFold
///   (succ (mul 2 m)) a k) m)`.
///
/// The `MapsInto` range bound (ADR-1015). By cases on `gaussSignNeg pp a
/// k`:
///
/// - **Not negative** (`false`, fold = `leastResidue pp a k`): positivity
///   is [`declare_least_residue_ne_zero_of_coprime`] at `k < pp` (derived
///   exactly as in [`declare_gauss_fold_injective_of_coprime`]). The upper
///   bound comes from `test = false`, i.e. `Not (ble succ_half lr = true)`
///   (`bool_false_ne_true`), hence `Not (Le succ_half lr)`
///   (`not_le_of_not_ble_eq_true`), hence `Lt lr succ_half`
///   (`lt_of_not_le`), hence `Le lr half` (`le_of_lt_succ`), and `half = m`
///   ([`declare_div_succ_two_mul_eq_self`]) finishes.
/// - **Negative** (`true`, fold = `sub pp (leastResidue pp a k)`):
///   positivity is [`sub_pos_of_lt`] from `leastResidue pp a k < pp`
///   (`mod_lt`). The upper bound comes from `test = true`, i.e. `Le
///   succ_half lr` (`le_of_ble_eq_true`), rewritten via `half = m` to `Le
///   (succ m) lr`; `add_le_add_left` at `m` gives `Le (add m (succ m)) (add
///   m lr)`, and `add m (succ m)` is defeq `pp` (two iota steps, same shape
///   as [`declare_div_succ_two_mul_eq_self`]'s bridge), so `sub_le_iff_le_
///   add`'s reverse direction turns `Le pp (add m lr)` into `Le (sub pp lr)
///   m`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gauss_fold_in_range(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_fold_in_range, 3, &|d, v| {
        let (m, a, k) = (v[0], v[1], v[2]);
        let two = d.num(2);
        let one = d.num(1);
        let zero = d.zero();
        let mul2m = d.mul(two, m);
        let pp = d.succ(mul2m);

        let gcd_a_pp = d.gcd(a, pp);
        let coprime_ty = d.eq(gcd_a_pp, one);
        let pos_k_ty = d.lt(zero, k);
        let le_k_m_ty = d.le(k, m);

        let fold_k = gauss_fold(d, &p, pp, a, k);
        let pos_fold_ty = d.lt(zero, fold_k);
        let le_fold_m_ty = d.le(fold_k, m);
        let concl = d.const_app(p.logic.and, &[pos_fold_ty, le_fold_m_ty]);

        let stmt = {
            let inner = d.arrow(le_k_m_ty, concl);
            let inner2 = d.arrow(pos_k_ty, inner);
            d.arrow(coprime_ty, inner2)
        };

        let coprime_fv = d.fresh_fvar();
        let coprime = d.kernel().fvar(coprime_fv);
        let pos_k_fv = d.fresh_fvar();
        let pos_k = d.kernel().fvar(pos_k_fv);
        let le_k_m_fv = d.fresh_fvar();
        let le_k_m = d.kernel().fvar(le_k_m_fv);

        let pos_pp = d.zero_lt_succ(mul2m);

        // k < pp, exactly as in gauss_fold_injective_of_coprime's proof.
        let pos_m = d.lemma(p.lt_of_lt_of_le, &[zero, k, m, pos_k, le_k_m]); // Lt zero m
        let lt_m_2m = d.lemma(p.lt_two_mul_of_pos, &[m, pos_m]); // Lt m mul2m
        let le_2m_pp = d.lemma(p.le_succ, &[mul2m]); // Le mul2m pp
        let lt_m_pp = d.lemma(p.lt_of_lt_of_le, &[m, mul2m, pp, lt_m_2m, le_2m_pp]); // Lt m pp
        let lt_k_pp = d.lemma(p.lt_of_le_of_lt, &[k, m, pp, le_k_m, lt_m_pp]); // Lt k pp

        let half = d.div(pp, two);
        let succ_half = d.succ(half);
        let lr = least_residue(d, &p, pp, a, k);
        let test = gauss_sign_neg(d, &p, pp, a, k);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let ty_true = d.bool_eq(test, true_);
        let ty_false = d.bool_eq(test, false_);
        let case = bool_true_or_false(d, &p, test);

        let half_eq_m = d.lemma(p.div_succ_two_mul_eq_self, &[m]); // Eq half m

        // Branch: test = true (negative).
        let branch_true = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let neg_k = d.sub(pp, lr);
            let eq_fold_neg = fold_eq_branch(d, &p, pp, a, k, true_, h); // Eq fold_k neg_k

            let ak = d.mul(a, k);
            let lr_lt_pp = d.lemma(p.mod_lt, &[ak, pp, pos_pp]); // Lt lr pp
            let pos_neg_k = sub_pos_of_lt(d, &p, lr, pp, lr_lt_pp); // Lt zero (sub pp lr)

            let le_succ_half_lr = d.lemma(p.le_of_ble_eq_true, &[succ_half, lr, h]); // Le succ_half lr
            let succ_m = d.succ(m);
            let succ_half_eq_succ_m = d.congr(half, m, half_eq_m, &|d, x| d.succ(x)); // Eq succ_half succ_m
            let le_motive = d.eq_motive(succ_half, &|d, x| d.le(x, lr));
            let le_succ_m_lr = d.transport(
                succ_half,
                le_motive,
                le_succ_half_lr,
                succ_m,
                succ_half_eq_succ_m,
            ); // Le succ_m lr

            let add_mono = d.lemma(p.add_le_add_left, &[m, succ_m, lr, le_succ_m_lr]); // Le (add m succ_m) (add m lr)
            let add_m_succm = d.add(m, succ_m);
            let add_m_lr = d.add(m, lr);
            // add m succ_m is defeq pp (two iota steps: add x (succ y) = succ
            // (add x y), then the outer succ matches pp's own succ mul2m
            // shape once add m m = mul2m -- built via two_mul_eq_add).
            let add_m_m_eq_mul2m = {
                let e = two_mul_eq_add(d, &p, m); // Eq mul2m (add m m)
                let add_m_m = d.add(m, m);
                d.symm(mul2m, add_m_m, e) // Eq (add m m) mul2m
            };
            let add_m_m = d.add(m, m);
            let congr_succ = d.congr(add_m_m, mul2m, add_m_m_eq_mul2m, &|d, x| d.succ(x)); // Eq (succ (add m m)) pp, defeq-usable as Eq add_m_succm pp
            let le_motive2 = d.eq_motive(add_m_succm, &|d, x| d.le(x, add_m_lr));
            let le_pp_addmlr = d.transport(add_m_succm, le_motive2, add_mono, pp, congr_succ); // Le pp (add m lr)

            let sub_iff = d.lemma(p.sub_le_iff_le_add, &[pp, lr, m]); // Iff (Le (sub pp lr) m) (Le pp (add m lr))
            let sub_target = d.le(neg_k, m);
            let add_target = d.le(pp, add_m_lr);
            let reverse = iff_reverse(d, sub_target, add_target, sub_iff);
            let le_negk_m = d.apply(reverse, &[le_pp_addmlr]); // Le neg_k m

            let pos_neg_k_ty = d.lt(zero, neg_k);
            let le_negk_m_ty = d.le(neg_k, m);
            let and_pf = and_intro2(d, &p, pos_neg_k_ty, le_negk_m_ty, pos_neg_k, le_negk_m);
            let eq_fold_neg_rev = d.symm(fold_k, neg_k, eq_fold_neg); // Eq neg_k fold_k
            let motive = d.eq_motive(neg_k, &|d, x| {
                let pos_x = d.lt(zero, x);
                let le_x_m = d.le(x, m);
                d.const_app(p.logic.and, &[pos_x, le_x_m])
            });
            let result = d.transport(neg_k, motive, and_pf, fold_k, eq_fold_neg_rev);
            d.lam_fv(h_fv, ty_true, result)
        };

        // Branch: test = false (not negative, identity).
        let branch_false = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let eq_fold_id = fold_eq_branch(d, &p, pp, a, k, false_, h); // Eq fold_k lr

            let pos_lr = d.lemma(
                p.least_residue_ne_zero_of_coprime,
                &[pp, a, k, coprime, pos_k, lt_k_pp],
            ); // Lt zero lr

            let htrue_fv = d.fresh_fvar();
            let htrue = d.kernel().fvar(htrue_fv);
            let hf_sym = d.bool_symm(test, false_, h); // Eq false_ test
            let combined = d.bool_trans(false_, test, true_, hf_sym, htrue); // Eq false_ true_
            let bool_false_ne_true = d.kernel().const_(p.logic.bool_false_ne_true, vec![]);
            let false_val = d.apply(bool_false_ne_true, &[combined]);
            let not_htrue = d.lam_fv(htrue_fv, ty_true, false_val); // Not (Eq test true_)

            let not_le = d.lemma(p.not_le_of_not_ble_eq_true, &[succ_half, lr, not_htrue]); // Not (Le succ_half lr)
            let lt_pf = d.lemma(p.lt_of_not_le, &[succ_half, lr, not_le]); // Lt lr succ_half
            let le_lr_half = d.lemma(p.le_of_lt_succ, &[lr, half, lt_pf]); // Le lr half

            let le_motive = d.eq_motive(half, &|d, x| d.le(lr, x));
            let le_lr_m = d.transport(half, le_motive, le_lr_half, m, half_eq_m); // Le lr m

            let pos_lr_ty = d.lt(zero, lr);
            let le_lr_m_ty = d.le(lr, m);
            let and_pf = and_intro2(d, &p, pos_lr_ty, le_lr_m_ty, pos_lr, le_lr_m);
            let eq_fold_id_rev = d.symm(fold_k, lr, eq_fold_id); // Eq lr fold_k
            let motive = d.eq_motive(lr, &|d, x| {
                let pos_x = d.lt(zero, x);
                let le_x_m = d.le(x, m);
                d.const_app(p.logic.and, &[pos_x, le_x_m])
            });
            let result = d.transport(lr, motive, and_pf, fold_k, eq_fold_id_rev);
            d.lam_fv(h_fv, ty_false, result)
        };

        let result = or_elim(
            d,
            &p,
            ty_true,
            ty_false,
            concl,
            branch_true,
            branch_false,
            case,
        );

        let with_le_k = d.lam_fv(le_k_m_fv, le_k_m_ty, result);
        let with_pos_k = d.lam_fv(pos_k_fv, pos_k_ty, with_le_k);
        let proof = d.lam_fv(coprime_fv, coprime_ty, with_pos_k);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.gaussFoldShift(pp, a, j) := pred (gaussFold pp a (succ j))` -- the
/// 0-indexed shift ADR-1015 sizes: `Int.prodRange_permute` needs a self-map
/// of `[0, m)`, not `[1, m]`.
fn gauss_fold_shift(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    j: ExprId,
) -> ExprId {
    let sj = d.succ(j);
    let fold = gauss_fold(d, p, pp, a, sj);
    d.pred(fold)
}

/// `Nat.gauss_fold_shift_maps_into : ∀ m a, gcd a (succ (mul 2 m)) = 1 →
///   MapsInto (fun j => pred (gaussFold (succ (mul 2 m)) a (succ j))) m`.
///
/// The shift wrapper's first half (ADR-1015). For `i < m`: `Lt i m` is
/// defeq `Le (succ i) m`, exactly [`declare_gauss_fold_in_range`]'s
/// hypothesis shape at `k := succ i`, so `hi` is reused directly with no
/// bridging lemma. `gauss_fold_in_range` gives `0 < gaussFold pp a (succ
/// i)` and `gaussFold pp a (succ i) ≤ m`; `succ_pred_of_pos` rewrites the
/// bound's LEFT side to `succ (pred (gaussFold pp a (succ i)))`, which is
/// defeq `Lt (pred (gaussFold pp a (succ i))) m` -- the goal, with no
/// further step.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gauss_fold_shift_maps_into(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_fold_shift_maps_into, 2, &|d, v| {
        let (m, a) = (v[0], v[1]);
        let two = d.num(2);
        let one = d.num(1);
        let nat = d.nat_ty();
        let mul2m = d.mul(two, m);
        let pp = d.succ(mul2m);

        let gcd_a_pp = d.gcd(a, pp);
        let coprime_ty = d.eq(gcd_a_pp, one);

        let sigma = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = gauss_fold_shift(d, &p, pp, a, j);
            d.lam_fv(j_fv, nat, body)
        };
        let concl = d.const_app(p.maps_into, &[sigma, m]);
        let stmt = d.arrow(coprime_ty, concl);

        let coprime_fv = d.fresh_fvar();
        let coprime = d.kernel().fvar(coprime_fv);

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(i, m);

        let succ_i = d.succ(i);
        let pos_succ_i = d.zero_lt_succ(i);
        let fold_si = gauss_fold(d, &p, pp, a, succ_i);

        let zero = d.zero();
        let and_pf = d.lemma(
            p.gauss_fold_in_range,
            &[m, a, succ_i, coprime, pos_succ_i, hi],
        ); // And (0 < fold_si) (Le fold_si m)  -- `hi` reused as `Le succ_i m`
        let pos_fold_si_ty = d.lt(zero, fold_si);
        let le_fold_si_m_ty = d.le(fold_si, m);
        let pos_fold_si = and_left(d, pos_fold_si_ty, le_fold_si_m_ty, and_pf);
        let le_fold_si_m = and_right(d, pos_fold_si_ty, le_fold_si_m_ty, and_pf);

        let succ_pred_eq = d.lemma(p.succ_pred_of_pos, &[fold_si, pos_fold_si]); // Eq fold_si (succ (pred fold_si))
        let pred_fold_si = d.pred(fold_si);
        let succ_pred_fold_si = d.succ(pred_fold_si);
        let motive = d.eq_motive(fold_si, &|d, x| d.le(x, m));
        let le_succpred_m = d.transport(
            fold_si,
            motive,
            le_fold_si_m,
            succ_pred_fold_si,
            succ_pred_eq,
        );
        // le_succpred_m : Le (succ (pred fold_si)) m, defeq `Lt (pred fold_si) m`.

        let with_hi = d.lam_fv(hi_fv, hi_ty, le_succpred_m);
        let with_i = d.lam_fv(i_fv, nat, with_hi);
        let proof = d.lam_fv(coprime_fv, coprime_ty, with_i);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.gauss_fold_shift_injective_on : ∀ m a, gcd a (succ (mul 2 m)) = 1 →
///   InjectiveOn (fun j => pred (gaussFold (succ (mul 2 m)) a (succ j))) m`.
///
/// The shift wrapper's second half (ADR-1015), completing piece 2:
/// `succ_pred_of_pos` lifts `heq : Eq (σ i) (σ j)` to `Eq (gaussFold pp a
/// (succ i)) (gaussFold pp a (succ j))` (positivity from
/// [`declare_gauss_fold_in_range`], same as
/// [`declare_gauss_fold_shift_maps_into`]);
/// [`declare_gauss_fold_injective_of_coprime`] gives `Eq (succ i) (succ
/// j)`; `succ_injective` strips the outer `succ`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gauss_fold_shift_injective_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_fold_shift_injective_on, 2, &|d, v| {
        let (m, a) = (v[0], v[1]);
        let two = d.num(2);
        let one = d.num(1);
        let nat = d.nat_ty();
        let mul2m = d.mul(two, m);
        let pp = d.succ(mul2m);

        let gcd_a_pp = d.gcd(a, pp);
        let coprime_ty = d.eq(gcd_a_pp, one);

        let sigma = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = gauss_fold_shift(d, &p, pp, a, j);
            d.lam_fv(j_fv, nat, body)
        };
        let concl = d.const_app(p.injective_on, &[sigma, m]);
        let stmt = d.arrow(coprime_ty, concl);

        let coprime_fv = d.fresh_fvar();
        let coprime = d.kernel().fvar(coprime_fv);

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(i, m);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let hj_ty = d.lt(j, m);

        let sig_i = gauss_fold_shift(d, &p, pp, a, i);
        let sig_j = gauss_fold_shift(d, &p, pp, a, j);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = d.eq(sig_i, sig_j);

        let succ_i = d.succ(i);
        let succ_j = d.succ(j);
        let pos_succ_i = d.zero_lt_succ(i);
        let pos_succ_j = d.zero_lt_succ(j);
        let fold_si = gauss_fold(d, &p, pp, a, succ_i);
        let fold_sj = gauss_fold(d, &p, pp, a, succ_j);

        let zero = d.zero();
        let and_pf_i = d.lemma(
            p.gauss_fold_in_range,
            &[m, a, succ_i, coprime, pos_succ_i, hi],
        );
        let pos_fold_si_ty = d.lt(zero, fold_si);
        let le_fold_si_m_ty = d.le(fold_si, m);
        let pos_fold_si = and_left(d, pos_fold_si_ty, le_fold_si_m_ty, and_pf_i);

        let and_pf_j = d.lemma(
            p.gauss_fold_in_range,
            &[m, a, succ_j, coprime, pos_succ_j, hj],
        );
        let pos_fold_sj_ty = d.lt(zero, fold_sj);
        let le_fold_sj_m_ty = d.le(fold_sj, m);
        let pos_fold_sj = and_left(d, pos_fold_sj_ty, le_fold_sj_m_ty, and_pf_j);

        let succ_pred_i = d.lemma(p.succ_pred_of_pos, &[fold_si, pos_fold_si]); // Eq fold_si (succ sig_i)
        let succ_pred_j = d.lemma(p.succ_pred_of_pos, &[fold_sj, pos_fold_sj]); // Eq fold_sj (succ sig_j)
        let succ_sig_i = d.succ(sig_i);
        let succ_sig_j = d.succ(sig_j);
        let succ_heq = d.congr(sig_i, sig_j, heq, &|d, x| d.succ(x)); // Eq succ_sig_i succ_sig_j
        let succ_pred_j_rev = d.symm(fold_sj, succ_sig_j, succ_pred_j); // Eq succ_sig_j fold_sj

        let (_e, fold_eq) = d.chain(
            fold_si,
            &[
                (succ_sig_i, succ_pred_i),
                (succ_sig_j, succ_heq),
                (fold_sj, succ_pred_j_rev),
            ],
        ); // Eq fold_si fold_sj

        let eq_succ = d.lemma(
            p.gauss_fold_injective_of_coprime,
            &[
                m, a, succ_i, succ_j, coprime, pos_succ_i, hi, pos_succ_j, hj, fold_eq,
            ],
        ); // Eq succ_i succ_j
        let eq_ij = d.lemma(p.succ_injective, &[i, j, eq_succ]); // Eq i j

        let with_heq = d.lam_fv(heq_fv, heq_ty, eq_ij);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        let proof = d.lam_fv(coprime_fv, coprime_ty, with_i);
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
    // The one lemma ADR-0990 flagged as genuinely absent while sizing
    // piece 2 (the pairing lemma): `leastResidue` never lands on `0` for
    // an in-range index when `a` is coprime to `pp`.
    declare_least_residue_ne_zero_of_coprime(d, p)?;
    // Piece 2 (ADR-0990): the signed-fold self-map and its injectivity on
    // `[1, m]`.
    declare_gauss_fold(d, p)?;
    declare_gauss_fold_injective_of_coprime(d, p)?;
    // ADR-1015: the MapsInto range bound's one missing arithmetic fact, the
    // range bound itself, and the 0-indexed shift wrapper -- completing
    // piece 2 (InjectiveOn + MapsInto on [0, m), directly what
    // Int.prodRange_permute consumes).
    declare_div_succ_two_mul_eq_self(d, p)?;
    declare_gauss_fold_in_range(d, p)?;
    declare_gauss_fold_shift_maps_into(d, p)?;
    declare_gauss_fold_shift_injective_on(d, p)?;
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

    /// Independent Rust-side recomputation for
    /// `least_residue_injective_of_coprime` -- re-run, not inherited, per
    /// this repository's standing rule that a "verified numerically" claim
    /// must be re-executed. At `pp := 7, a := 3` (coprime), the least-residue
    /// map `k ↦ (a*k) mod pp` is injective on `{0,…,6}` -- brute force.
    /// Negative control: at `a := pp` (NOT coprime, `gcd(7,7)=7≠1`), the map
    /// collapses -- `k=1` and `k=2` collide -- confirming the coprimality
    /// hypothesis is genuinely load-bearing, not vacuous.
    #[test]
    fn least_residue_map_is_injective_at_a_coprime_witness_and_collides_without_coprimality() {
        let pp: u32 = 7;
        let a: u32 = 3;
        let residues: Vec<u32> = (0..pp).map(|k| (a * k) % pp).collect();
        let mut sorted = residues.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            residues.len(),
            "leastResidue(pp:=7, a:=3, ·) must be injective on [0,7) -- gcd(3,7)=1"
        );

        let a_bad: u32 = 7; // gcd(7,7) = 7, not coprime to pp
        assert_eq!(
            (a_bad * 1) % pp,
            (a_bad * 2) % pp,
            "negative control: without coprimality the map collides at k=1,k=2 \
             (both give residue 0) -- the coprimality hypothesis is not vacuous"
        );
    }

    /// `gaussFold` computed at `pp := 7` (`m := 3`), `a := 2` -- independent
    /// Rust-side recomputation, re-run rather than inherited, per this
    /// repository's standing rule. `leastResidue 7 2 k` is `2, 4, 6` for
    /// `k = 1, 2, 3`; the sign threshold is `r >= 4`, so `k=1` is NOT
    /// negative (fold = 2) while `k=2,3` ARE (fold = 7-4=3, 7-6=1). All
    /// three fold values are distinct, matching
    /// `gauss_fold_injective_of_coprime`'s conclusion -- checked here by the
    /// kernel's own reduction, both positively (the exact values) and
    /// negatively (pairwise distinctness), per the standing rule that a
    /// symbolic accept needs a concrete check too (a defeq-shaped gap can
    /// hide behind a symbolic proof the kernel otherwise accepts).
    #[test]
    fn gauss_fold_computes_the_signed_representative_and_is_injective_at_pp_seven() {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut d = super::NatDev::new(&mut k, p);

        let pp = d.num(7);
        let a = d.num(2);
        let k1 = d.num(1);
        let k2 = d.num(2);
        let k3 = d.num(3);

        let fold1 = gauss_fold(&mut d, &p, pp, a, k1);
        let fold2 = gauss_fold(&mut d, &p, pp, a, k2);
        let fold3 = gauss_fold(&mut d, &p, pp, a, k3);

        let e1 = d.num(2);
        let e2 = d.num(3);
        let e3 = d.num(1);
        assert!(
            d.kernel().def_eq(fold1, e1),
            "gaussFold 7 2 1 must reduce to 2 (leastResidue 2, not negative)"
        );
        assert!(
            d.kernel().def_eq(fold2, e2),
            "gaussFold 7 2 2 must reduce to 3 (leastResidue 4, negative -> 7-4)"
        );
        assert!(
            d.kernel().def_eq(fold3, e3),
            "gaussFold 7 2 3 must reduce to 1 (leastResidue 6, negative -> 7-6)"
        );
        assert!(
            !d.kernel().def_eq(fold1, fold2),
            "negative control: distinct k must give distinct fold values (1 vs 2)"
        );
        assert!(
            !d.kernel().def_eq(fold2, fold3),
            "negative control: distinct k must give distinct fold values (2 vs 3)"
        );
        assert!(
            !d.kernel().def_eq(fold1, fold3),
            "negative control: distinct k must give distinct fold values (1 vs 3)"
        );

        // The theorem itself applies at a concrete instance -- m := 3, a := 2,
        // k := k2 := 1, heq := refl fold1 -- confirming the kernel accepts a
        // fully-applied instance of `gauss_fold_injective_of_coprime`
        // (m := 3 so `succ (mul 2 m)` reduces to `pp := 7` above).
        let m = d.num(3);
        let gcd_a_pp = d.gcd(a, pp);
        let one = d.num(1);
        assert!(
            d.kernel().def_eq(gcd_a_pp, one),
            "gcd 2 7 must reduce to 1 (sanity check on the coprimality witness)"
        );
        let coprime = d.refl(one); // Eq (gcd a pp) one, via defeq gcd_a_pp = one
        // Lt zero k1, defeq Le (succ zero) k1 = Le k1 k1 (k1 = succ zero by
        // construction) -- `Nat.le` is a primitive inductive, not `Eq`, so
        // this needs `le_refl`, not `Eq.refl`.
        let pos_k1 = d.lemma(p.le_refl, &[k1]);
        let le_k1_m = {
            // Le k1 m, i.e. Le 1 3 -- via le_add_right(1, 2): Le 1 (add 1 2) = Le 1 3.
            let two = d.num(2);
            d.lemma(p.le_add_right, &[k1, two])
        };
        let heq_refl = d.refl(fold1);
        let result = d.lemma(
            p.gauss_fold_injective_of_coprime,
            &[
                m, a, k1, k1, coprime, pos_k1, le_k1_m, pos_k1, le_k1_m, heq_refl,
            ],
        );
        let expected = d.eq(k1, k1);
        let inferred = d
            .kernel()
            .infer(result)
            .expect("gauss_fold_injective_of_coprime must apply at a concrete instance");
        assert!(
            d.kernel().def_eq(inferred, expected),
            "the applied instance's type must be Eq k1 k1"
        );
    }
    /// `Nat.div_succ_two_mul_eq_self`, `Nat.gauss_fold_in_range`,
    /// `Nat.gauss_fold_shift_maps_into` and
    /// `Nat.gauss_fold_shift_injective_on` (ADR-1015, piece 2's completion)
    /// each apply at a concrete instance -- `pp := 7` (`m := 3`), `a := 2`,
    /// mirroring the existing `pp := 7` instance above so the two tests'
    /// numerals cross-check each other.
    #[test]
    fn gauss_fold_range_bound_and_shift_wrapper_apply_at_pp_seven() {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut d = super::NatDev::new(&mut k, p);

        let pp = d.num(7);
        let a = d.num(2);
        let m = d.num(3);
        let k1 = d.num(1);
        let zero = d.zero();
        let two = d.num(2);

        // div_succ_two_mul_eq_self: Eq (div pp 2) m, i.e. div 7 2 = 3.
        let div_eq = d.lemma(p.div_succ_two_mul_eq_self, &[m]);
        let div_pp_two = d.div(pp, two);
        let div_inferred = d
            .kernel()
            .infer(div_eq)
            .expect("div_succ_two_mul_eq_self must apply at m := 3");
        let expect_div_eq = d.eq(div_pp_two, m);
        assert!(
            d.kernel().def_eq(div_inferred, expect_div_eq),
            "div_succ_two_mul_eq_self(3) must state Eq (div 7 2) 3"
        );
        assert!(
            d.kernel().def_eq(div_pp_two, m),
            "sanity: div 7 2 must reduce to 3"
        );

        // Reusable witnesses at k1 := 1 -- Lt zero k1 (le_refl(1)) and
        // Le k1 m (le_add_right(1, 2)); the latter is ALSO exactly `Lt zero
        // m` by defeq (succ zero = k1), reused below for i0 := zero.
        let coprime_gcd = d.gcd(a, pp);
        let one = d.num(1);
        let coprime = d.refl(one);
        assert!(
            d.kernel().def_eq(coprime_gcd, one),
            "sanity: gcd 2 7 must reduce to 1"
        );
        let pos_k1 = d.lemma(p.le_refl, &[k1]);
        let le_k1_m = d.lemma(p.le_add_right, &[k1, two]);

        // gauss_fold_in_range: And (0 < gaussFold 7 2 1) (Le (gaussFold 7 2 1) 3).
        let fold1 = gauss_fold(&mut d, &p, pp, a, k1);
        let range_pf = d.lemma(p.gauss_fold_in_range, &[m, a, k1, coprime, pos_k1, le_k1_m]);
        let range_inferred = d
            .kernel()
            .infer(range_pf)
            .expect("gauss_fold_in_range must apply at a concrete instance");
        let expect_range = {
            let pos_ty = d.lt(zero, fold1);
            let le_ty = d.le(fold1, m);
            d.const_app(p.logic.and, &[pos_ty, le_ty])
        };
        assert!(
            d.kernel().def_eq(range_inferred, expect_range),
            "gauss_fold_in_range(3,2,1) must give And (0 < gaussFold 7 2 1) (gaussFold 7 2 1 <= 3)"
        );

        // gauss_fold_shift_maps_into applied at i0 := 0 (hi0 := le_k1_m,
        // which IS `Lt zero m` by defeq): Lt (pred (gaussFold 7 2 1)) 3,
        // i.e. Lt 1 3 (pred 2 = 1).
        let maps_into_pf = d.lemma(p.gauss_fold_shift_maps_into, &[m, a, coprime]);
        let i0 = zero;
        let hi0 = le_k1_m;
        let maps_into_applied = d.apply(maps_into_pf, &[i0, hi0]);
        let sigma_i0 = d.pred(fold1);
        let maps_into_inferred = d
            .kernel()
            .infer(maps_into_applied)
            .expect("gauss_fold_shift_maps_into must apply at i0 := 0");
        let expect_maps_into = d.lt(sigma_i0, m);
        assert!(
            d.kernel().def_eq(maps_into_inferred, expect_maps_into),
            "gauss_fold_shift_maps_into(3,2) at i0 := 0 must give Lt (pred (gaussFold 7 2 1)) 3"
        );
        let one_lit = d.num(1);
        assert!(
            d.kernel().def_eq(sigma_i0, one_lit),
            "sanity: pred (gaussFold 7 2 1) = pred 2 = 1"
        );

        // gauss_fold_shift_injective_on applied at i := j := 0, heq := refl:
        // Eq 0 0.
        let inj_pf = d.lemma(p.gauss_fold_shift_injective_on, &[m, a, coprime]);
        let heq_refl = d.refl(sigma_i0);
        let inj_applied = d.apply(inj_pf, &[i0, i0, hi0, hi0, heq_refl]);
        let inj_inferred = d
            .kernel()
            .infer(inj_applied)
            .expect("gauss_fold_shift_injective_on must apply at i := j := 0");
        let expect_inj = d.eq(i0, i0);
        assert!(
            d.kernel().def_eq(inj_inferred, expect_inj),
            "gauss_fold_shift_injective_on(3,2) at i := j := 0 must give Eq 0 0"
        );
    }
}
